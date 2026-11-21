-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaSignStoppedBounds
import BeaconcryptCore.Computational.RegistrationNativeMldsaDynamicBounds

/-! Dynamic ordinal tracking adds no ML signing slot. The complete original free program retains the combined bundle/build bound even though the observed key is learned only at its actual successful generation attempt. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaSignDynamicBounds
open Classical
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaOpaque (handleSource)
open RegistrationNativeMldsaDynamicGame (program continued observe)
open RegistrationNativeMldsaGhostState (track)
open RegistrationNativeMldsaSignBounds (IsSigningCallback)
open RegistrationNativeMldsaEufTapeCosts (IsSign)
variable {n : Nat} {ι KemSK V : Type} {base : OracleSpec ι}
variable (source : RegistrationNativeMldsa.Source)
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)

private theorem predicate (query : (RegistrationNativeMldsaProgram.Spec (handleSource source)).Domain) :
    RegistrationNativeMldsaSignBounds.IsSign query ↔ IsSign source query := by
  cases query with
  | inl coin => rfl
  | inr query => cases query <;> rfl

private theorem callback (selected : Nat) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential (handleSource source))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeMldsaDynamicGame.State (n := n) (KemSK := KemSK) source) :
    ((track source selected (RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential query)).run before).IsQueryBoundP
      (IsSign source) (if IsSigningCallback query then 1 else 0) := by
  simp only [track, StateT.run, isQueryBoundP_map_iff]
  apply RegistrationNativeMldsaGenerationGhost.bounded
  exact (isQueryBoundP_congr_pred (predicate source)).mp
    (RegistrationNativeMldsaSignBounds.handler setup checks wire route representation created credential query before.1)

private theorem stopped (selected : Nat) (initial : RegistrationNativeExperiment.Initial n KemSK (handleSource source))
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V) (cap : Nat)
    (bounded : work.IsQueryBoundP IsSigningCallback cap) (ghost : RegistrationNativeMldsaGenerationGhost.State) :
    ((simulateQ (RegistrationNativeMldsaStop.freeze
      (fun query => track source selected (RegistrationNativeMldsaProfile.handler setup checks wire route representation initial.created initial.credential query))
      (observe source) RegistrationNativeMldsaTableStop.defaultReply) work).run ((initial.state, ghost), none)).IsQueryBoundP
        (IsSign source) cap := by
  apply bounded.simulateQ_run_StateT_of_step _ ((initial.state, ghost), none)
  intro query current
  rcases current with ⟨current, previous⟩
  cases previous with
  | none =>
      simpa only [RegistrationNativeMldsaStop.freeze, RegistrationNativeMldsaStop.monitor,
        StateT.run, bind_pure_comp, isQueryBoundP_map_iff] using
        callback source setup checks wire route representation selected initial.created initial.credential query current
  | some candidate => trivial

/-- Complete ordinal-only source execution has its actual typed bundle/build signing cap. -/
theorem typed (adversary : RegistrationNativeExperiment.Public → OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (cap : Nat) (bounded : ∀ publicValue, (adversary publicValue).IsQueryBoundP IsSigningCallback cap)
    (selected : Nat) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64) :
    (program (n := n) source setup checks wire route representation adversary selected ensureInit identityIndex serverKeyId).IsQueryBoundP
      (IsSign source) cap := by
  unfold program
  rw [← Nat.zero_add cap]
  apply isQueryBoundP_bind
    (RegistrationNativeMldsaGenerationGhost.bounded source selected _ (IsSign source) 0
      ((isQueryBoundP_congr_pred (predicate source)).mp
        (RegistrationNativeMldsaSignBounds.start (n := n) (source := handleSource source) setup ensureInit identityIndex serverKeyId)) {})
  intro initialized _possible
  cases initial_eq : initialized.1 with
  | none =>
      simp only [continued, initial_eq]
      trivial
  | some initial =>
      simp only [continued, initial_eq, isQueryBoundP_map_iff]
      exact stopped source setup checks wire route representation selected initial (adversary initial.public) cap
        (bounded initial.public) initialized.2

/-- Every unchanged raw native mode yields the concrete qBundle+qBuild signing cap for the ordinal-only source program. -/
theorem compiled (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (selected : Nat) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64) :
    (program (n := n) source setup checks wire route representation
      (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue))
      selected ensureInit identityIndex serverKeyId).IsQueryBoundP (IsSign source) (budget.bundle + budget.build) := by
  apply typed source setup checks wire route representation _ (budget.bundle + budget.build) _ selected ensureInit identityIndex serverKeyId
  intro publicValue
  exact RegistrationNativeMldsaSignStoppedBounds.compile_bound setup wire publicValue.serverKeyId bounds mode
    (adversary publicValue) budget (bounded publicValue)
end BeaconcryptCore.Computational.RegistrationNativeMldsaSignDynamicBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSignDynamicBounds.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSignDynamicBounds.typed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSignDynamicBounds.compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSignDynamicBounds.compiled
