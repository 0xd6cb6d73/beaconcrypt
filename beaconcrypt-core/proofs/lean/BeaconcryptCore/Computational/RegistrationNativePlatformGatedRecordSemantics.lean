-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordFlat
import BeaconcryptCore.Computational.CborRawRecordFlatSemantics
/-! Equal-length hidden sends retain identical full gated executions in the zeroed world. Both private attempted-send effects and all subsequent public reserve effects remain present. Caller-known escape persistence and the exact ledger coin step are derived for this same interpreter. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordSemantics
open PqxdhRecordLiftInterface (Environment WorldSpec)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhRecordLiftIdeal (KeyMode CtxPrivate ctxInterpreter)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftFlat (KnownAt zeros coinStep support_keep_oracle support_run_fst)
open PqxdhDeploymentInterface (Spec FullSpec Handle FreshBounds)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformGatedRecordFlat (State fold native full)
attribute [local irreducible] fold RegistrationNativePlatformGatedRecordInterface.closed ctxInterpreter CborRawRecordOriginService.native
variable {n : Nat} {ι : Type} {base : OracleSpec ι} {KemSK Reader Response E S A Failure : Type}

private theorem fold_pure (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (value : A) :
    fold service codec route (pure value : StateT E (OracleComp (WorldSpec n)) A) = pure value := by
  funext before
  unfold fold
  change RegistrationNativePlatformGatedRecordFlat.join <$>
    CborRawRecordOriginFlatten.interpret service codec route (pure (value, before.1.1.1)) before.1.1.2 before.1.2 before.2 =
      pure (value, before)
  rw [CborRawRecordOriginFlatten.interpret_pure, map_pure]
  rfl

/-- Public post-send work cannot discard the caller-known classification of any installed handle. -/
theorem fold_known (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : StateT E (OracleComp (WorldSpec n)) A) (before : State n E S) (handle : Handle)
    (known : KnownAt before.1.2 handle) (result : A × State n E S)
    (supported : result ∈ support ((fold service codec route work).run before)) : KnownAt result.2.1.2 handle := by
  unfold fold at supported
  change result ∈ support (RegistrationNativePlatformGatedRecordFlat.join <$>
    CborRawRecordOriginFlatten.interpret service codec route (work.run before.1.1.1) before.1.1.2 before.1.2 before.2) at supported
  rw [support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact support_keep_oracle (PqxdhRecordLiftProtocol.handler codec.frameRead route)
    (fun control => KnownAt control handle) (PqxdhRecordLiftFlat.handler_known codec.frameRead route handle)
    _ before.1.2 known inner.1 (support_run_fst _ _ _ inner reached)

/-- Every actual gated native query preserves the source escape invariant. -/
theorem native_known (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (query : Spec.Domain)
    (before : State n E S) (handle : Handle) (known : KnownAt before.1.2 handle)
    (result : Spec.Range query × State n E S)
    (supported : result ∈ support ((native service env reserve codec route query).run before)) : KnownAt result.2.1.2 handle :=
  fold_known service codec route _ before handle known result supported

/-- The whole canonical private send is retained before the same source capacity gate is interpreted. -/
theorem send_split (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (handle : Handle) (plaintext : Pqxdh.Bytes)
    (before : State n E S) :
    (simulateQ (native service env reserve codec route) (PqxdhDeploymentSecrecy.send handle plaintext)).run before =
      ((simulateQ (CborRawRecordOriginService.native service env codec route)
        (PqxdhDeploymentSecrecy.send handle plaintext)).run before >>= fun result =>
          (fold service codec route (RegistrationNativePlatformGatedRecordInterface.closed
            (RegistrationNativePlatformOrdinaryGate.gate reserve (fun value => value.ciphertext.length) result.1))).run result.2) := by
  cases handle <;> simp only [PqxdhDeploymentSecrecy.send, simulateQ_spec_query,
    RegistrationNativePlatformGatedRecordFlat.native_split, StateT.run_bind,
    RegistrationNativePlatformGatedRecordInterface.post]
  all_goals rfl

/-- Byte shifts of a hidden send give exactly the same private and public execution after zeroing, including allocator failures and retries. -/
theorem send_zeros (modes : Label n → KeyMode) (setup : Setup base KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (handle : Handle) (first second : Pqxdh.Bytes) (length : first.length = second.length)
    (before : State n E (CtxPrivate n)) (notKnown : ¬KnownAt before.1.2 handle) :
    (simulateQ (native (ctxInterpreter modes zeros setup codec) env reserve codec route)
      (PqxdhDeploymentSecrecy.send handle first)).run before =
    (simulateQ (native (ctxInterpreter modes zeros setup codec) env reserve codec route)
      (PqxdhDeploymentSecrecy.send handle second)).run before := by
  rw [send_split, send_split]
  have same := CborRawRecordFlatSemantics.nativeImpl_send_zeros modes setup codec route env handle first second length before notKnown
  have aliases : CborRawRecordFlat.nativeImpl modes zeros setup codec route env =
      CborRawRecordOriginService.native (ctxInterpreter modes zeros setup codec) env codec route := by
    unfold CborRawRecordFlat.nativeImpl CborRawRecordOriginService.native
    rfl
  rw [aliases] at same
  have paired := congrArg (fun work : ProbComp (Option RawCtxSourceSend.Encrypted × State n E (CtxPrivate n)) => work >>= fun result =>
    (fold (ctxInterpreter modes zeros setup codec) codec route (RegistrationNativePlatformGatedRecordInterface.closed
      (RegistrationNativePlatformOrdinaryGate.gate reserve (fun value => value.ciphertext.length) result.1))).run result.2) same
  convert paired using 1

/-- Ledger message and test-bit coins still make exactly one original native uniform step and no reserve call. -/
theorem coin (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (amount : Nat) (before : State n E (CtxPrivate n)) :
    (native (ctxInterpreter modes replace setup codec) env reserve codec route (.inl amount)).run before =
      (fun reply => (reply, (before.1, coinStep before.2))) <$> (unifSpec.query amount : ProbComp _) := by
  rw [RegistrationNativePlatformGatedRecordFlat.native_split]
  simp only [RegistrationNativePlatformGatedRecordInterface.post, fold_pure, bind_pure]
  have aliases : CborRawRecordFlat.nativeImpl modes replace setup codec route env =
      CborRawRecordOriginService.native (ctxInterpreter modes replace setup codec) env codec route := by
    unfold CborRawRecordFlat.nativeImpl CborRawRecordOriginService.native
    rfl
  rw [← aliases]
  exact CborRawRecordFlatSemantics.nativeImpl_coin modes replace setup codec route env amount before

/-- Flattening the original ledger keeps the post-send allocator below its record and test/fresh updates. -/
theorem full_run (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (serverKid : U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (ledger : PqxdhDeploymentSecrecy.Ledger) (before : State n E S) :
    (full service env reserve crypto codec route serverKid bounds query).run (ledger, before) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (native service env reserve codec route)
          ((PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds query).run ledger)).run before := rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordSemantics

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordSemantics.fold_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordSemantics.fold_known

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordSemantics.native_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordSemantics.native_known

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordSemantics.send_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordSemantics.send_split

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordSemantics.send_zeros' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordSemantics.send_zeros

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordSemantics.coin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordSemantics.coin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordSemantics.full_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordSemantics.full_run
