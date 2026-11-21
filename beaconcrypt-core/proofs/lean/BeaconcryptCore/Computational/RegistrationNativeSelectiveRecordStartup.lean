-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordCounts
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenStartup
import BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyStartup
import BeaconcryptCore.Computational.RegistrationNativeRecordPackage

/-! The complete effectful selective native startup and original ledger have actual World query bills. Constructor and ML generation retain their explicit coin caps; the existing one-hash allowance covers its pure fixed pin construction. Startup performs no ongoing record request. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordStartup
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (WorldSpec EffectKind coinLift effectLift)
open PqxdhRecordLiftBudget (WorldEffect WorldRecord RecordKind recordBudget)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeSelectiveEntropyEnvironment (State)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

theorem coins_effect (kind : EffectKind) (work : ProbComp Value) (count : Nat) (bounded : work.IsTotalQueryBound count) :
    (simulateQ (coinLift (n := n)) work).IsQueryBoundP (WorldEffect kind) (if kind = .coin then count else 0) := by
  cases kind with
  | coin =>
      apply RawCtxSourceOpen.simulate_bound coinLift (fun _ => True) (WorldEffect .coin) work count
        ((isQueryBoundP_true_iff _ _).mpr bounded)
      intro query
      simp [coinLift, WorldEffect, PqxdhRecordLiftInterface.effectKind, isQueryBoundP_query_iff]
  | hash =>
      apply (isQueryBoundP_false work 0).simulateQ_of_step
      all_goals simp [coinLift, WorldEffect, PqxdhRecordLiftInterface.effectKind, isQueryBoundP_query_iff]
  | administrative =>
      apply (isQueryBoundP_false work 0).simulateQ_of_step
      all_goals simp [coinLift, WorldEffect, PqxdhRecordLiftInterface.effectKind, isQueryBoundP_query_iff]

theorem coins_record (kind : RecordKind) (work : ProbComp Value) :
    (simulateQ (coinLift (n := n)) work).IsQueryBoundP (WorldRecord kind) 0 := by
  apply (isQueryBoundP_false work 0).simulateQ_of_step
  all_goals simp [coinLift, WorldRecord, isQueryBoundP_query_iff]

private theorem constructor_metadata (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (count : Nat)
    (bounded : ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()).IsTotalQueryBound count) :
    ((PqxdhLiveServerConstruction.construct (P := Std.Array Std.U8 151#usize) setup.joint ensureInit identityIndex serverKeyId none).run ()).IsTotalQueryBound count := by
  have erased : (fun _ => ()) <$> ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()) =
      (fun _ => ()) <$> ((PqxdhLiveServerConstruction.construct (P := Std.Array Std.U8 151#usize) setup.joint ensureInit identityIndex serverKeyId none).run ()) := by
    simp only [PqxdhLiveServerConstruction.construct, StateT.run, map_bind]
    refine bind_congr fun ready => ?_
    split <;> simp only [Functor.map_map, map_pure]
  have mapped : ((fun _ => ()) <$> ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ())).IsTotalQueryBound count := by
    simpa only [IsTotalQueryBound, isQueryBound_map_iff] using bounded
  rw [erased] at mapped
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using mapped

def startupCost (constructorCoins mlCoins : Nat) : EffectKind → Nat
  | .coin => constructorCoins + mlCoins
  | .hash => 1
  | .administrative => 0

theorem start_effect (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity) (constructorCoins mlCoins : Nat)
    (constructorBound : ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()).IsTotalQueryBound constructorCoins)
    (mlBound : (RegistrationNativeMldsa.generate source).IsTotalQueryBound mlCoins) (kind : EffectKind) :
    (RegistrationNativeHiddenStartup.start (n := n) setup source ensureInit identityIndex serverKeyId identity).IsQueryBoundP
      (WorldEffect kind) (startupCost constructorCoins mlCoins kind) := by
  have constructor151 := constructor_metadata setup ensureInit identityIndex serverKeyId constructorCoins constructorBound
  have bounded :
      (RegistrationNativeHiddenStartup.start (n := n) setup source ensureInit identityIndex serverKeyId identity).IsQueryBoundP
        (WorldEffect kind) ((if kind = .coin then constructorCoins else 0) +
          ((if kind = .coin then mlCoins else 0) + (if kind = .hash then 1 else 0))) := by
    unfold RegistrationNativeHiddenStartup.start
    apply isQueryBoundP_bind (coins_effect kind _ constructorCoins constructor151)
    intro constructed _
    cases built : constructed.1 with
    | none => trivial
    | some created =>
        apply isQueryBoundP_bind (coins_effect kind _ mlCoins mlBound)
        intro generated _
        cases sampled : generated with
        | none => trivial
        | some credential =>
            cases kind <;> simp [WorldEffect]
  cases kind <;> simpa only [startupCost, ite_true, ite_false, reduceCtorEq, Nat.add_zero, Nat.zero_add] using bounded

theorem start_record (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity) (kind : RecordKind) :
    (RegistrationNativeHiddenStartup.start (n := n) setup source ensureInit identityIndex serverKeyId identity).IsQueryBoundP
      (WorldRecord kind) 0 := by
  unfold RegistrationNativeHiddenStartup.start
  apply isQueryBoundP_bind (m := 0) (coins_record kind _)
  intro constructed _
  cases built : constructed.1 with
  | none => trivial
  | some created =>
      apply isQueryBoundP_bind (m := 0) (coins_record kind _)
      intro generated _
      cases sampled : generated with
      | none => trivial
      | some credential => simp [WorldRecord]

variable {source : RegistrationNativeMldsa.Source}

def outcome (native : RegistrationNativeSelectiveEntropyStartup.Outcome n KemSK ProviderState Value source) :
    RegistrationNativeEntropyRun.Outcome (State n KemSK ProviderState source) Value :=
  native.map (fun finished => (PqxdhRegistrationJointServerBirth.encode finished.1, finished.2.1.1,
    (finished.2.1.2, finished.2.2)))

section Program
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (source : RegistrationNativeMldsa.Source)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (providerState : ProviderState)
  (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)

noncomputable def program : OracleComp (WorldSpec n) (RegistrationNativeEntropyRun.Outcome (State n KemSK ProviderState source) Value) :=
  outcome <$> RegistrationNativeSelectiveHiddenStartup.program setup checks wire source ensureInit identityIndex serverKeyId
    seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary

/-- The record-ideal endpoint runs precisely the actual effectful startup AST with the same initial CTX cache. -/
theorem ideal_source (route : RawCtxServerRouting.SenderDecoder)
    (modes : PqxdhRecordLiftWorldCompiler.Label n → PqxdhRecordLiftIdeal.KeyMode) :
    RegistrationNativeRecordPackage.View.result <$>
      RegistrationNativeRecordPackage.ctx modes setup (RegistrationNativeWire.ledgerCodec wire) route
        (program (n := n) setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
          selectedOwner selectedAccept bounds mode adversary) =
      (fun result => result.1.1) <$>
        RegistrationNativeSelectiveEntropyStartup.run modes id setup checks wire route source ensureInit identityIndex serverKeyId
          seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary PqxdhRecordLiftIdeal.CtxPrivate.initial := by
  rw [RegistrationNativeRecordPackage.ctx_result_source]
  simp only [program, RegistrationNativeSelectiveEntropyStartup.run, CborRawRecordOriginFlatten.interpret,
    simulateQ_map, StateT.run_map, Functor.map_map]
  rfl

variable (budget : PqxdhDeploymentInterface.Budget)
  (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))

include bounded in
/-- Actual native initialization is record-free, so the complete selective program retains exactly the original joint record budget. -/
theorem program_record (kind : RecordKind) :
    (program (n := n) setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
      selectedOwner selectedAccept bounds mode adversary).IsQueryBoundP (WorldRecord kind) (recordBudget budget kind) := by
  simp only [program, isQueryBoundP_map_iff, RegistrationNativeSelectiveHiddenStartup.program]
  refine (isQueryBoundP_bind (m := recordBudget budget kind)
    (start_record setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed) kind) ?_).mono (by omega)
  intro initialized _
  cases initialized with
  | none => trivial
  | some born =>
      simp only [bind_pure_comp, isQueryBoundP_map_iff]
      exact RegistrationNativeSelectiveRecordCounts.run_bound setup checks wire source seed scalar candidate provider selectedOwner selectedAccept
        born.native.credential serverKeyId bounds mode budget
        (adversary ⟨setup.joint.publicKeys seed, born.native.credential.publicKey, serverKeyId⟩)
        (bounded ⟨setup.joint.publicKeys seed, born.native.credential.publicKey, serverKeyId⟩) born.native.frontend
        (RegistrationNativeSelectiveHiddenInterpreter.initial providerState) kind

variable (allowance : Fin 14 → EffectKind → Nat)
  (framed : RegistrationNativeSelectiveRecordFrame.Frame (n := n) setup checks wire source seed scalar candidate provider selectedOwner selectedAccept allowance)
  (constructorCoins mlCoins : Nat)
  (constructorBound : ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()).IsTotalQueryBound constructorCoins)
  (mlBound : (RegistrationNativeMldsa.generate source).IsTotalQueryBound mlCoins)

def effectTotal (kind : EffectKind) : Nat :=
  startupCost constructorCoins mlCoins kind +
    (PqxdhRecordLiftBudget.directCost budget bounds kind + (PqxdhRecordLiftInterface.Caps.mk budget 0).envTotal allowance kind)

include bounded framed constructorBound mlBound in
/-- The full native program pays its actual startup coins and one shared ML-pin hash, plus original direct ledger work and per-command native frame allowances. -/
theorem program_effect (kind : EffectKind) :
    (program (n := n) setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
      selectedOwner selectedAccept bounds mode adversary).IsQueryBoundP (WorldEffect kind)
      (effectTotal bounds budget allowance constructorCoins mlCoins kind) := by
  simp only [program, isQueryBoundP_map_iff, RegistrationNativeSelectiveHiddenStartup.program, effectTotal]
  apply isQueryBoundP_bind (start_effect setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed)
    constructorCoins mlCoins constructorBound mlBound kind)
  intro initialized _
  cases initialized with
  | none => trivial
  | some born =>
      simp only [bind_pure_comp, isQueryBoundP_map_iff]
      have counted := RegistrationNativeSelectiveRecordFrame.wrapped_bound setup checks wire source seed scalar candidate provider selectedOwner selectedAccept
        allowance framed born.native.credential serverKeyId bounds mode budget
        (adversary ⟨setup.joint.publicKeys seed, born.native.credential.publicKey, serverKeyId⟩)
        (bounded ⟨setup.joint.publicKeys seed, born.native.credential.publicKey, serverKeyId⟩)
        (born.native.frontend, RegistrationNativeSelectiveHiddenInterpreter.initial providerState) kind
      rw [← RegistrationNativeSelectiveEntropyExecution.run_source, isQueryBoundP_map_iff] at counted
      exact counted

end Program

end BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordStartup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordStartup.coins_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordStartup.coins_effect

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordStartup.coins_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordStartup.coins_record

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordStartup.start_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordStartup.start_effect

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordStartup.start_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordStartup.start_record

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordStartup.ideal_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordStartup.ideal_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordStartup.program_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordStartup.program_record

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordStartup.program_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordStartup.program_effect
