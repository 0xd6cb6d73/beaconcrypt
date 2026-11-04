-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperimentRouting
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceOrdinaryLens
/-! Actual public ongoing sends run the unchanged record request before the public terminal writer gate. The gate receives only ciphertext length. Incoming raw routes issue no writer request. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSyntax
open RegistrationNativePlatformPublicSourceOrdinaryLens (oldProgram publicWork)
variable {n : Nat} {KemSK Platform E : Type} {source : RegistrationNativeMldsa.Source}

def after (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (work : StateT (RegistrationNativePublicFrontend.State source)
      (OracleComp (RegistrationNativePublicFrontend.Spec n KemSK)) (Option RawCtxSourceSend.Encrypted)) :
    RegistrationNativePlatformPublicFrontend.M n KemSK Platform source (Option RawCtxSourceSend.Encrypted) := do
  let output ← oldProgram work
  publicWork (RegistrationNativePlatformOrdinaryGate.gate reserve (fun value => value.ciphertext.length) output)

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem public_coin {A : Type} (work : ProbComp A) :
    simulateQ (RegistrationNativePlatformPublicFrontend.embedLocal (n := n) (KemSK := KemSK))
      (simulateQ RegistrationNativePlatformPublicFrontend.localCoin work) =
      simulateQ RegistrationNativePlatformPublicFrontend.publicCoin work := by
  rw [← QueryImpl.simulateQ_compose]
  rfl

private theorem public_run {A : Type} (work : StateT Platform ProbComp A)
    (before : RegistrationNativePlatformPublicFrontend.State source Platform) :
    (publicWork (n := n) (KemSK := KemSK) work) before =
      (fun result => (result.1, (before.1, result.2))) <$>
        simulateQ RegistrationNativePlatformPublicFrontend.publicCoin (work.run before.2) := by
  simp only [publicWork, RegistrationNativePlatformPublicFrontend.executeLocal,
    RegistrationNativePlatformPublicFrontend.platform, StateT.run, simulateQ_map, public_coin]

private theorem bind_apply {S A B : Type} {m : Type → Type} [Monad m]
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m]
    (value : A) (before : S) : (pure value : StateT S m A) before = pure (value, before) := rfl

private theorem gate_platform (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (output : Option RawCtxSourceSend.Encrypted) (previous : Platform) :
    (RegistrationNativePlatformOrdinaryGate.gate
      (fun amount => RegistrationNativePlatformPublicFrontend.platformFull (n := n) (KemSK := KemSK) (reserve amount))
      (fun value => value.ciphertext.length) output) previous =
      simulateQ RegistrationNativePlatformPublicFrontend.publicCoin
        ((RegistrationNativePlatformOrdinaryGate.gate reserve (fun value => value.ciphertext.length) output).run previous) := by
  cases output with
  | none => simp only [RegistrationNativePlatformOrdinaryGate.gate, pure_apply, StateT.run_pure, simulateQ_pure]
  | some value =>
    simp only [RegistrationNativePlatformOrdinaryGate.gate, bind_apply,
      RegistrationNativePlatformPublicFrontend.platformFull, StateT.run, simulateQ_bind]
    apply bind_congr
    intro result
    cases result.1 <;> simp only [simulateQ_pure, pure_apply]

/-- Actual Server send syntax retains the attempted record before the terminal allocation decision. -/
theorem server_send (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (keyId : U64) (plaintext : Pqxdh.Bytes) :
    RegistrationNativePlatformPublicFrontend.record (n := n) (KemSK := KemSK) (source := source) reserve (.inl (.inl (plaintext, keyId))) =
      after reserve (RegistrationNativePublicFrontend.record (.inl (.inl (plaintext, keyId)))) := by
  funext before
  simp only [RegistrationNativePlatformPublicFrontend.record, after, oldProgram,
    RegistrationNativePublicFrontend.record, StateT.run, StateT.monad_bind_def, StateT.bind,
    simulateQ_map, simulateQ_spec_query, bind_map_left, public_run, gate_platform, bind_pure_comp]
  rfl

/-- Actual Beacon send syntax resolves the stored World owner and applies the same terminal public gate. -/
theorem beacon_send (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (index : Nat) (plaintext : Pqxdh.Bytes) :
    RegistrationNativePlatformPublicFrontend.record (n := n) (KemSK := KemSK) (source := source) reserve (.inr (index, .inl plaintext)) =
      after reserve (RegistrationNativePublicFrontend.record (.inr (index, .inl plaintext))) := by
  funext before
  cases found : before.1.beacons[index]? with
  | none =>
    simp only [RegistrationNativePlatformPublicFrontend.record, after, oldProgram,
      RegistrationNativePublicFrontend.record, StateT.run, StateT.monad_bind_def, StateT.bind,
      found, simulateQ_pure, pure_bind, public_run, RegistrationNativePlatformOrdinaryGate.gate,
      simulateQ_pure, map_pure, pure_apply]
  | some owner =>
    simp only [RegistrationNativePlatformPublicFrontend.record, after, oldProgram,
      RegistrationNativePublicFrontend.record, StateT.run, StateT.monad_bind_def, StateT.bind,
      found, simulateQ_map, simulateQ_spec_query, bind_map_left, public_run, gate_platform, bind_pure_comp]
    rfl

/-- Incoming Server raw syntax has no runtime writer leaf. -/
theorem server_raw (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (raw : Pqxdh.Bytes) :
    RegistrationNativePlatformPublicFrontend.record (n := n) (KemSK := KemSK) (source := source) reserve (.inl (.inr raw)) =
      oldProgram (RegistrationNativePublicFrontend.record (.inl (.inr raw))) := by
  funext before
  simp only [RegistrationNativePlatformPublicFrontend.record, oldProgram,
    RegistrationNativePublicFrontend.record, StateT.run, simulateQ_map, simulateQ_spec_query, Functor.map_map]

/-- Incoming Beacon raw syntax preserves actual absent-owner and reached-owner branches without a writer request. -/
theorem beacon_raw (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (index : Nat) (raw : Pqxdh.Bytes) :
    RegistrationNativePlatformPublicFrontend.record (n := n) (KemSK := KemSK) (source := source) reserve (.inr (index, .inr raw)) =
      oldProgram (RegistrationNativePublicFrontend.record (.inr (index, .inr raw))) := by
  funext before
  cases found : before.1.beacons[index]? <;>
    simp only [RegistrationNativePlatformPublicFrontend.record, oldProgram,
      RegistrationNativePublicFrontend.record, StateT.run, found, simulateQ_pure,
      simulateQ_map, simulateQ_spec_query, map_pure, Functor.map_map]
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSyntax

namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSource
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePlatformPublicSourceExecution (State execute)
open RegistrationNativePlatformPublicSourceOrdinaryLens (oldProgram publicWork)
open RegistrationNativePublicSourceState (project restore nativeView)
open RegistrationServerReferenceRestore (Roots)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

/-- The literal ordinary record primitive executes on the exact current private World and leaves P untouched. -/
theorem old_record (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (roots : Roots)
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State n KemSK Platform source) :
    (fun result => ((result.1, project roots scalar result.2.1.1 result.2.2), result.2.1.2)) <$>
      (execute setup wire route sign seed scalar (oldProgram (RegistrationNativePublicFrontend.record query))).run before =
      (fun result => ((result.1, nativeView result.2), before.1.2)) <$>
        (RegistrationNativeExperiment.record setup wire route query source).run (restore roots scalar before.1.1 before.2) := by
  rw [RegistrationNativePlatformPublicSourceOrdinaryLens.old_source, Functor.map_map]
  have original := RegistrationNativePublicSourceWorld.record_source setup wire route sign seed scalar roots query (before.1.1, before.2)
  have mapped := congrArg (fun action => (fun result => ((result.1, result.2), before.1.2)) <$> action) original
  simpa only [Functor.map_map, Prod.map_def, id_eq] using mapped

private theorem mapped_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

/-- The actual public terminal gate retains the reached private record state on every reservation outcome. -/
theorem server_gated (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (roots : Roots)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (keyId : U64) (plaintext : Pqxdh.Bytes) (before : State n KemSK Platform source) :
    (fun result => ((result.1, project roots scalar result.2.1.1 result.2.2), result.2.1.2)) <$>
      (execute setup wire route sign seed scalar (RegistrationNativePlatformPublicRecordSyntax.after reserve
        (RegistrationNativePublicFrontend.record (.inl (.inl (plaintext, keyId)))))).run before = (do
      let result ← (RegistrationNativeExperiment.record setup wire route (.inl (.inl (plaintext, keyId))) source).run (restore roots scalar before.1.1 before.2)
      let allowed ← (RegistrationNativePlatformOrdinaryGate.gate reserve (fun value => value.ciphertext.length) result.1).run before.1.2
      pure ((allowed.1, nativeView result.2), allowed.2)) := by
  have original := old_record setup wire route sign seed scalar roots (.inl (.inl (plaintext, keyId))) before
  have mapped := congrArg (fun action => action >>= fun result =>
    (fun allowed => ((allowed.1, result.1.2), allowed.2)) <$>
      (RegistrationNativePlatformOrdinaryGate.gate reserve (fun value => value.ciphertext.length) result.1.1).run result.2) original
  convert mapped using 1 <;> simp only [RegistrationNativePlatformPublicRecordSyntax.after,
    RegistrationNativePlatformPublicSourceExecution.execute_bind, map_bind,
    RegistrationNativePlatformPublicSourceOrdinaryLens.public_source,
    bind_map_left, bind_pure_comp, Functor.map_map]
  all_goals rfl

/-- The actual public terminal gate retains the reached private record state on every reservation outcome. -/
theorem beacon_gated (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (roots : Roots)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (index : Nat) (plaintext : Pqxdh.Bytes) (before : State n KemSK Platform source) :
    (fun result => ((result.1, project roots scalar result.2.1.1 result.2.2), result.2.1.2)) <$>
      (execute setup wire route sign seed scalar (RegistrationNativePlatformPublicRecordSyntax.after reserve
        (RegistrationNativePublicFrontend.record (.inr (index, .inl plaintext))))).run before = (do
      let result ← (RegistrationNativeExperiment.record setup wire route (.inr (index, .inl plaintext)) source).run (restore roots scalar before.1.1 before.2)
      let allowed ← (RegistrationNativePlatformOrdinaryGate.gate reserve (fun value => value.ciphertext.length) result.1).run before.1.2
      pure ((allowed.1, nativeView result.2), allowed.2)) := by
  have original := old_record setup wire route sign seed scalar roots (.inr (index, .inl plaintext)) before
  have mapped := congrArg (fun action => action >>= fun result =>
    (fun allowed => ((allowed.1, result.1.2), allowed.2)) <$>
      (RegistrationNativePlatformOrdinaryGate.gate reserve (fun value => value.ciphertext.length) result.1.1).run result.2) original
  convert mapped using 1 <;> simp only [RegistrationNativePlatformPublicRecordSyntax.after,
    RegistrationNativePlatformPublicSourceExecution.execute_bind, map_bind,
    RegistrationNativePlatformPublicSourceOrdinaryLens.public_source,
    bind_map_left, bind_pure_comp, Functor.map_map]
  all_goals rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSyntax.server_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSyntax.server_send

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSyntax.beacon_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSyntax.beacon_send

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSyntax.server_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSyntax.server_raw

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSyntax.beacon_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSyntax.beacon_raw

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSource.old_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSource.old_record

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSource.server_gated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSource.server_gated

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSource.beacon_gated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSource.beacon_gated
