-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaCoinCompilerBounds
import BeaconcryptCore.Computational.RegistrationNativeMldsaCoinPrimitives
import BeaconcryptCore.Computational.RegistrationNativeMldsaCoinCallbacks
import BeaconcryptCore.Computational.RegistrationNativeMldsaDynamicBounds

/-! The original typed resource contract gives a concrete all-replies ordinary-uniform allowance for the actual initialized, stopped source program. Primitive receipts constrain only the actual initializer and KEM algorithms. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaCoinStoppedBounds
open Classical

private theorem simulation {Query Target State Value : Type} {queries : OracleSpec Query} {target : OracleSpec Target}
    (handler : QueryImpl queries (StateT State (OracleComp target)))
    (predicate : Target → Prop) [DecidablePred predicate] (step : Nat)
    (cost : ∀ query current, ((handler query).run current).IsQueryBoundP predicate step)
    (work : OracleComp queries Value) (cap : Nat) (bounded : work.IsTotalQueryBound cap) (before : State) :
    ((simulateQ handler work).run before).IsQueryBoundP predicate (cap * step) := by
  induction work using OracleComp.inductionOn generalizing cap before with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isTotalQueryBound_query_bind_iff] at bounded
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      apply (isQueryBoundP_bind (cost query before) (fun middle _ => ih middle.1 _ (bounded.2 middle.1) middle.2)).mono
      exact Nat.le_of_eq (by rw [Nat.sub_one_mul, Nat.add_sub_cancel' (Nat.le_mul_of_pos_left step bounded.1)])

private theorem frozen_simulation {Query Target State Candidate Value : Type} {queries : OracleSpec Query} {target : OracleSpec Target}
    (handler : QueryImpl queries (StateT State (OracleComp target)))
    (predicate : Target → Prop) [DecidablePred predicate] (step : Nat)
    (cost : ∀ query current, ((handler query).run current).IsQueryBoundP predicate step)
    (observe : RegistrationNativeMldsaStop.Observer (spec := queries) (State := State) (Candidate := Candidate))
    (defaultReply : (query : queries.Domain) → queries.Range query)
    (work : OracleComp queries Value) (cap : Nat) (bounded : work.IsTotalQueryBound cap)
    (before : State) (previous : Option Candidate) :
    ((simulateQ (RegistrationNativeMldsaStop.freeze handler observe defaultReply) work).run
      (before, previous)).IsQueryBoundP predicate (cap * step) := by
  apply simulation _ predicate step _ work cap bounded (before, previous)
  intro query current
  rcases current with ⟨current, previous⟩
  cases previous with
  | none =>
    simpa only [RegistrationNativeMldsaStop.freeze, RegistrationNativeMldsaStop.monitor, StateT.run,
      bind_pure_comp, isQueryBoundP_map_iff] using cost query current
  | some candidate => exact isQueryBoundP_pure _ _ _

open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (handleSource)
open RegistrationNativeMldsaCoinPrimitives (IsCoin)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def total (qInit qTyped qKeygen qEncap qDecap : Nat) : Nat :=
  qInit + 32 + 64 + qTyped * RegistrationNativeMldsaCoinCallbacks.allowance qKeygen qEncap qDecap

/-- The source allowance is a polynomial in the original typed-command total and the narrow primitive draw caps. -/
theorem total_eq (qInit qTyped qKeygen qEncap qDecap : Nat) :
    total qInit qTyped qKeygen qEncap qDecap =
      qInit + 96 + qTyped * (2305 + qKeygen + 9 * qEncap + 9 * qDecap) := by
  simp only [total, RegistrationNativeMldsaCoinCallbacks.allowance_eq]

/-- The actual typed stopped source pays only the derived literal callback allowance for each original typed query, including failed prefixes and arbitrary raw ML replies. -/
theorem stopped {Candidate : Type} {source : Source} (setup : Setup base KemSK) (checks : Checks)
    (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : Credential source)
    (kem : RegistrationNativeKemSourceBills.Caps setup)
    (observe : RegistrationNativeMldsaStop.Observer (spec := RegistrationNativeRawAdapter.TypedSpec)
      (State := RegistrationNativeExperiment.State n KemSK source) (Candidate := Candidate))
    (defaultReply : (query : RegistrationNativeRawAdapter.TypedSpec.Domain) → RegistrationNativeRawAdapter.TypedSpec.Range query)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (cap : Nat)
    (bounded : work.IsTotalQueryBound cap) (before : RegistrationNativeExperiment.State n KemSK source)
    (previous : Option Candidate) :
    ((simulateQ (RegistrationNativeMldsaStop.freeze
      (RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential)
      observe defaultReply) work).run (before, previous)).IsQueryBoundP IsCoin
      (cap * RegistrationNativeMldsaCoinCallbacks.allowance kem.keygen kem.encapsulate kem.decapsulate) := by
  apply frozen_simulation _ IsCoin _ _ observe defaultReply work cap bounded before previous
  intro query current
  exact RegistrationNativeMldsaCoinCallbacks.handler setup checks wire route representation created credential kem query current

/-- Actual startup plus complete stopped adaptive execution has an explicit source-uniform cap; no callback-cost frame is assumed. -/
theorem program (source : Source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (kem : RegistrationNativeKemSourceBills.Caps setup)
    (adversary : RegistrationNativeExperiment.Public → OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (cap : Nat) (bounded : ∀ publicValue, (adversary publicValue).IsTotalQueryBound cap)
    (ensureInit : StateT Unit ProbComp Bool) (qInit : Nat) (initialization : (ensureInit.run ()).IsTotalQueryBound qInit)
    (identityIndex : Nat) (serverKid : Std.U64) (publicKey : RegistrationNativeMldsaEuf.PublicKey) :
    (RegistrationNativeMldsaStoppedGame.program (n := n) source setup checks wire route representation adversary
      ensureInit identityIndex serverKid publicKey).IsQueryBoundP (RegistrationNativeMldsaEufTapeCosts.IsCoin source)
      (total qInit cap kem.keygen kem.encapsulate kem.decapsulate) := by
  apply (isQueryBoundP_congr_pred (p := IsCoin) (p' := RegistrationNativeMldsaEufTapeCosts.IsCoin source)
    (fun query => by cases query <;> rfl)).mp
  unfold RegistrationNativeMldsaStoppedGame.program total
  apply isQueryBoundP_bind (RegistrationNativeMldsaCoinPrimitives.start (source := handleSource source)
    setup ensureInit qInit initialization identityIndex serverKid)
  intro initialized _
  cases initialized with
  | none => trivial
  | some initial =>
    rw [RegistrationNativeMldsaStoppedGame.continued, isQueryBoundP_map_iff]
    exact stopped setup checks wire route representation initial.created initial.credential kem _
      RegistrationNativeMldsaTableStop.defaultReply (adversary initial.public) cap (bounded initial.public) initial.state none

/-- Every original raw observation mode gives a fully instantiated source-uniform cap from its original selective command budget. -/
theorem compiled (source : Source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (kem : RegistrationNativeKemSourceBills.Caps setup)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (ensureInit : StateT Unit ProbComp Bool) (qInit : Nat) (initialization : (ensureInit.run ()).IsTotalQueryBound qInit)
    (identityIndex : Nat) (serverKid : Std.U64) (publicKey : RegistrationNativeMldsaEuf.PublicKey) :
    (RegistrationNativeMldsaStoppedGame.program (n := n) source setup checks wire route representation
      (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue))
      ensureInit identityIndex serverKid publicKey).IsQueryBoundP (RegistrationNativeMldsaEufTapeCosts.IsCoin source)
      (total qInit (RegistrationNativeMldsaCoinCompilerBounds.total bounds budget) kem.keygen kem.encapsulate kem.decapsulate) := by
  apply program source setup checks wire route representation kem _ _ _ ensureInit qInit initialization identityIndex serverKid publicKey
  intro publicValue
  exact RegistrationNativeMldsaCoinCompilerBounds.compile setup.source.crypto wire publicValue.serverKeyId bounds mode
    (adversary publicValue) budget (bounded publicValue)


private theorem tracked_callback (source : Source) (setup : Setup base KemSK) (checks : Checks)
    (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (kem : RegistrationNativeKemSourceBills.Caps setup) (selected : Nat)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : Credential (handleSource source))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeMldsaDynamicGame.State (n := n) (KemSK := KemSK) source) :
    ((RegistrationNativeMldsaGhostState.track source selected
      (RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential query)).run before).IsQueryBoundP
      (RegistrationNativeMldsaEufTapeCosts.IsCoin source)
      (RegistrationNativeMldsaCoinCallbacks.allowance kem.keygen kem.encapsulate kem.decapsulate) := by
  simp only [RegistrationNativeMldsaGhostState.track, StateT.run, isQueryBoundP_map_iff]
  apply RegistrationNativeMldsaGenerationGhost.bounded
  exact (isQueryBoundP_congr_pred (p := IsCoin) (p' := RegistrationNativeMldsaEufTapeCosts.IsCoin source)
    (fun call => by cases call <;> rfl)).mp
    (RegistrationNativeMldsaCoinCallbacks.handler setup checks wire route representation created credential kem query before.1)

/-- Learning the target from its actual generation reply and tracking its ordinal adds no ordinary uniform request. -/
theorem dynamic (source : Source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (kem : RegistrationNativeKemSourceBills.Caps setup)
    (adversary : RegistrationNativeExperiment.Public → OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (cap : Nat) (bounded : ∀ publicValue, (adversary publicValue).IsTotalQueryBound cap)
    (selected : Nat) (ensureInit : StateT Unit ProbComp Bool) (qInit : Nat) (initialization : (ensureInit.run ()).IsTotalQueryBound qInit)
    (identityIndex : Nat) (serverKid : Std.U64) :
    (RegistrationNativeMldsaDynamicGame.program (n := n) source setup checks wire route representation adversary selected
      ensureInit identityIndex serverKid).IsQueryBoundP (RegistrationNativeMldsaEufTapeCosts.IsCoin source)
      (total qInit cap kem.keygen kem.encapsulate kem.decapsulate) := by
  unfold RegistrationNativeMldsaDynamicGame.program total
  apply isQueryBoundP_bind
    (RegistrationNativeMldsaGenerationGhost.bounded source selected _ (RegistrationNativeMldsaEufTapeCosts.IsCoin source) (qInit + 32 + 64)
      ((isQueryBoundP_congr_pred (p := IsCoin) (p' := RegistrationNativeMldsaEufTapeCosts.IsCoin source)
        (fun query => by cases query <;> rfl)).mp
        (RegistrationNativeMldsaCoinPrimitives.start (n := n) (source := handleSource source)
          setup ensureInit qInit initialization identityIndex serverKid)) {})
  intro initialized _
  cases initial_eq : initialized.1 with
  | none => simp only [RegistrationNativeMldsaDynamicGame.continued, initial_eq]; trivial
  | some initial =>
    simp only [RegistrationNativeMldsaDynamicGame.continued, initial_eq, isQueryBoundP_map_iff]
    exact frozen_simulation _ (RegistrationNativeMldsaEufTapeCosts.IsCoin source) _
      (tracked_callback source setup checks wire route representation kem selected initial.created initial.credential)
      _ RegistrationNativeMldsaTableStop.defaultReply (adversary initial.public) cap (bounded initial.public) (initial.state, initialized.2) none

/-- The unchanged raw resource contract also bounds every actual ordinal-only dynamic source program by the same concrete polynomial allowance. -/
theorem dynamic_compiled (source : Source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (kem : RegistrationNativeKemSourceBills.Caps setup)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (selected : Nat) (ensureInit : StateT Unit ProbComp Bool) (qInit : Nat) (initialization : (ensureInit.run ()).IsTotalQueryBound qInit)
    (identityIndex : Nat) (serverKid : Std.U64) :
    (RegistrationNativeMldsaDynamicGame.program (n := n) source setup checks wire route representation
      (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue))
      selected ensureInit identityIndex serverKid).IsQueryBoundP (RegistrationNativeMldsaEufTapeCosts.IsCoin source)
      (total qInit (RegistrationNativeMldsaCoinCompilerBounds.total bounds budget) kem.keygen kem.encapsulate kem.decapsulate) := by
  apply dynamic source setup checks wire route representation kem _ _ _ selected ensureInit qInit initialization identityIndex serverKid
  intro publicValue
  exact RegistrationNativeMldsaCoinCompilerBounds.compile setup.source.crypto wire publicValue.serverKeyId bounds mode
    (adversary publicValue) budget (bounded publicValue)

/-- The actual ordinary-EUF reduction pays explicit initializer/KEM/native-source coins, reserved nonselected generation and source signature costs, with no desired resource premise. -/
theorem reduction_coins (source : Source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (kem : RegistrationNativeKemSourceBills.Caps setup)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (ensureInit : StateT Unit ProbComp Bool) (qInit : Nat) (initialization : (ensureInit.run ()).IsTotalQueryBound qInit)
    (identityIndex : Nat) (serverKid : Std.U64)
    (qGenerate qSign : Nat) (generation : source.generate.IsTotalQueryBound qGenerate)
    (signing : ∀ key request, (source.sign key request).IsTotalQueryBound qSign)
    (target : Fin (budget.create + 1)) (publicKey : RegistrationNativeMldsaEuf.PublicKey) :
    (RegistrationNativeMldsaEufTapeReduction.adversary source target
      (RegistrationNativeMldsaStoppedGame.program (n := n) source setup checks wire route representation
        (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue))
        ensureInit identityIndex serverKid) publicKey).IsQueryBoundP RegistrationNativeMldsaChosen.IsUniform
      (qGenerate * budget.create +
        (total qInit (RegistrationNativeMldsaCoinCompilerBounds.total bounds budget) kem.keygen kem.encapsulate kem.decapsulate +
          qSign * (budget.bundle + budget.build))) :=
  RegistrationNativeMldsaEufTapeCosts.reduction_coins source qGenerate qSign generation signing target _ publicKey _ _
    (compiled source setup checks wire route representation kem bounds mode adversary budget bounded ensureInit qInit initialization identityIndex serverKid publicKey)
    (RegistrationNativeMldsaSignStoppedBounds.compiled source setup checks wire route representation bounds mode adversary budget bounded ensureInit identityIndex serverKid publicKey)

/-- Both external primitive resources of the same actual ordinary-EUF adversary follow from the original raw command budget and narrow primitive draw receipts. -/
theorem reduction_resources (source : Source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (kem : RegistrationNativeKemSourceBills.Caps setup)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (ensureInit : StateT Unit ProbComp Bool) (qInit : Nat) (initialization : (ensureInit.run ()).IsTotalQueryBound qInit)
    (identityIndex : Nat) (serverKid : Std.U64)
    (qGenerate qSign : Nat) (generation : source.generate.IsTotalQueryBound qGenerate)
    (signing : ∀ key request, (source.sign key request).IsTotalQueryBound qSign)
    (target : Fin (budget.create + 1)) (publicKey : RegistrationNativeMldsaEuf.PublicKey) :
    let reduction := RegistrationNativeMldsaEufTapeReduction.adversary source target
      (RegistrationNativeMldsaStoppedGame.program (n := n) source setup checks wire route representation
        (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue))
        ensureInit identityIndex serverKid) publicKey
    reduction.IsQueryBoundP RegistrationNativeMldsaChosen.IsSigning (budget.bundle + budget.build) ∧
      reduction.IsQueryBoundP RegistrationNativeMldsaChosen.IsUniform
        (qGenerate * budget.create +
          (total qInit (RegistrationNativeMldsaCoinCompilerBounds.total bounds budget) kem.keygen kem.encapsulate kem.decapsulate +
            qSign * (budget.bundle + budget.build))) := by
  constructor
  · exact RegistrationNativeMldsaSignStoppedBounds.reduction_signs source setup checks wire route representation
      bounds mode adversary budget bounded ensureInit identityIndex serverKid target publicKey
  · exact reduction_coins source setup checks wire route representation kem bounds mode adversary budget bounded
      ensureInit qInit initialization identityIndex serverKid qGenerate qSign generation signing target publicKey

end BeaconcryptCore.Computational.RegistrationNativeMldsaCoinStoppedBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinStoppedBounds.stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinStoppedBounds.stopped

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinStoppedBounds.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinStoppedBounds.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinStoppedBounds.compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinStoppedBounds.compiled

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinStoppedBounds.dynamic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinStoppedBounds.dynamic

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinStoppedBounds.dynamic_compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinStoppedBounds.dynamic_compiled

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinStoppedBounds.reduction_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinStoppedBounds.reduction_coins

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinStoppedBounds.total_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinStoppedBounds.total_eq

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinStoppedBounds.reduction_resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinStoppedBounds.reduction_resources
