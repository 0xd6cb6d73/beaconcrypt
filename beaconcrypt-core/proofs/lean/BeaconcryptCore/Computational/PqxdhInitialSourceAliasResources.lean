import BeaconcryptCore.Computational.PqxdhInitialSourceAliases
import BeaconcryptCore.Computational.PqxdhInitialSourceInitialResources
import BeaconcryptCore.Computational.PqxdhInitialAliasQueryBounds

/-! The value-consistent full-source endpoint pays all original callback coins plus every possible initializer root miss. Its independent32-byte root and shared64 response are charged before the complete adaptive source. The conservative bound counts native76-byte children, commitment64-byte draws and all supplied public/base/decapsulation callback costs. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialSourceAliasResources
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhInitialSourceInitialSecrecy PqxdhInitialSourceFirstResources PqxdhInitialNativeBudgets
open PqxdhInitialObserverCallbackBudgets
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}
local notation "SourceInput" => Input extra M P I D K X Response A N S B
local notation "SourceContext" => Context extra M P I D K X Response A N S B
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (qPost qCheck qKnown qPre qApplication qSelector qAux : Nat)
local notation "cap" => callbackCap (PqxdhInitialSourceInitialResources.budget qPre qApplication qSelector qAux)
local notation "U" => PqxdhInitialSourceInitialResources.uniformCap qPost qPre qApplication qSelector qAux

/-- Every original source callback retains its complete ordinary computation; the initializer query is separately charged by the root interpreter. -/
theorem step_coins (input : SourceInput) (caps : Caps input qPost qCheck qKnown qPre qApplication qSelector qAux)
    (stage : Nat)
    (query : (PqxdhInitialSourceAliasCompiler.SourceSpec (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (S := S) (B := B)).Domain)
    (state : PqxdhInitialSourceAliasCompiler.LocalState A N) :
    ((PqxdhInitialSourceAliasCompiler.compiler source writer stage (PqxdhInitialSourceAliases.plain input) query).run state).IsQueryBoundP IsCoin cap := by
  cases query with
  | inl query =>
    refine (coins_uniform _ (liveCost query) ?_).mono ?_
    · simpa only [RawCtxSelectiveFamilyLog.handler, StateT.run, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
        live_uniform source writer stage query state.1.1
    · rcases query with ((request | opening) | ((request | sealing) | (coin | (hash | hkdf)))) | read
      all_goals simp only [liveCost, publicCost, callbackCap]
      all_goals omega
  | inr query =>
    rcases query with preparation | (application | (initializer | (selector | auxiliary)))
    · refine (coins_uniform _ qPre ?_).mono ?_
      · simpa only [PqxdhInitialSourceAliases.plain, StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using caps.preBound preparation (state.1.1.1, state.2) ∅
      · simp only [callbackCap, PqxdhInitialSourceInitialResources.budget]
        omega
    · refine (coins_uniform _ qApplication ?_).mono ?_
      · simpa only [PqxdhInitialSourceAliases.plain, StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using caps.applicationBound application (state.1.1.1, state.2) ∅
      · simp only [callbackCap, PqxdhInitialSourceInitialResources.budget]
        omega
    · simp [PqxdhInitialSourceAliasCompiler.compiler, StateT.run, IsCoin]
    · refine (coins_uniform _ qSelector ?_).mono ?_
      · simpa only [PqxdhInitialSourceAliases.plain, StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using caps.selectorBound selector (state.1.1.1, state.2) ∅
      · simp only [callbackCap, PqxdhInitialSourceInitialResources.budget]
        omega
    · refine (coins_uniform _ qAux ?_).mono ?_
      · simpa only [PqxdhInitialSourceAliases.plain, StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using caps.auxBound auxiliary (state.1.1.1, state.2) ∅
      · simp only [callbackCap, PqxdhInitialSourceInitialResources.budget]
        omega

/-- The complete original source client pays the original total callback allowance times the explicit native/external maximum. -/
theorem program_coins {Result : Type} (input : SourceInput)
    (caps : Caps input qPost qCheck qKnown qPre qApplication qSelector qAux) (stage : Nat)
    (client : OracleComp (PqxdhInitialSourceAliasCompiler.SourceSpec (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (S := S) (B := B)) Result)
    (queries : Nat) (bounded : client.IsTotalQueryBound queries) (state : PqxdhInitialSourceAliasCompiler.LocalState A N) :
    ((simulateQ (PqxdhInitialSourceAliasCompiler.compiler source writer stage (PqxdhInitialSourceAliases.plain input)) client).run state).IsQueryBoundP IsCoin (queries * cap) := by
  exact PqxdhBeaconPhase2Bounds.interpreted_total_bound _ IsCoin cap queries
    (step_coins source writer qPost qCheck qKnown qPre qApplication qSelector qAux input caps stage) client bounded state

/-- The first shared initializer lookup adds no ordinary coin; all complete original source work is charged before interpreting initializer misses. -/
theorem client_coins (input : SourceInput)
    (caps : Caps input qPost qCheck qKnown qPre qApplication qSelector qAux) (stage : Nat) :
    (PqxdhInitialSourceAliases.client source writer sender route decode stage (.inr input)).IsQueryBoundP IsCoin U := by
  apply (isQueryBoundP_map_iff _ _ _).mpr
  unfold PqxdhInitialSourceAliasCompiler.client
  refine (isQueryBoundP_bind (m := U) (show (PqxdhInitialLabelCompiler.Spec.query (.inr (.family input.selectedMessage)) : OracleComp PqxdhInitialLabelCompiler.Spec _).IsQueryBoundP IsCoin 0 by simp [IsCoin]) ?_).mono ?_
  · intro response _
    apply program_coins source writer qPost qCheck qKnown qPre qApplication qSelector qAux input caps stage _ (7 + qPost * 67)
    exact PqxdhInitialOriginPost.sequence_total source _ _ _ sender route decode input.index input.metadata _ input.post qPost caps.postBound _
  · omega

variable (prior : ProbComp (Context extra M P I D K X Response A N S B))

/-- Each cut of the exact source sampler pays all original coins and the conservative32-byte allowance for every initializer attempt. -/
theorem cut_uniform
    (caps : ∀ input : Input extra M P I D K X Response A N S B, Sum.inr input ∈ support prior → Caps input qPost qCheck qKnown qPre qApplication qSelector qAux)
    (stage : Nat) (cut : PqxdhInitialAliasBound.Cut (Bool ⊕ {input : Input extra M P I D K X Response A N S B // Sum.inr input ∈ support prior})) :
    (PqxdhInitialAliasBound.right source
      (fun context => PqxdhInitialSourceAliases.selected (PqxdhInitialSourceAliases.erase prior context))
      (fun context => PqxdhInitialSourceAliases.client source writer sender route decode stage (PqxdhInitialSourceAliases.erase prior context)) cut).IsTotalQueryBound
      (U + 32 * (1 + (7 + qPost * 67))) := by
  unfold PqxdhInitialAliasBound.right
  apply (isQueryBound_map_iff _ _ _ _ _).mpr
  rw [← QueryImpl.simulateQ_compose]
  apply PqxdhInitialAliasQueryBounds.program source _ cut.1.2 _ _ U (1 + (7 + qPost * 67))
  · cases context : cut.1.1 with
    | inl decision => trivial
    | inr input => exact client_coins source writer sender route decode qPost qCheck qKnown qPre qApplication qSelector qAux input.val (caps input.val input.property) stage
  · cases context : cut.1.1 with
    | inl decision => trivial
    | inr input =>
      apply (isQueryBoundP_congr_pred (p := IsService) (p' := PqxdhInitialRootAliases.IsInitializer)
        (fun query => by cases query <;> simp [IsService, PqxdhInitialRootAliases.IsInitializer])).mpr
      exact PqxdhInitialSourceAliases.client_initial source writer sender route decode stage input.val qPost (caps input.val input.property).postBound

/-- The value-consistent final source endpoint pays the complete actual preparation, independent root32, shared64 response, original callback work and all initializer cache misses. -/
theorem consistent_uniform
    (caps : ∀ input : Input extra M P I D K X Response A N S B, Sum.inr input ∈ support prior → Caps input qPost qCheck qKnown qPre qApplication qSelector qAux)
    (stage qPrior : Nat) (bounded : prior.IsTotalQueryBound qPrior) :
    (PqxdhInitialSourceAliases.consistent source writer sender route decode prior stage).IsTotalQueryBound
      ((qPrior + (32 + 64)) + (U + 32 * (1 + (7 + qPost * 67)))) := by
  unfold PqxdhInitialSourceAliases.consistent PqxdhInitialAliasEvent.rightGame
  apply isTotalQueryBound_bind
  · unfold PqxdhInitialAliasBound.sampleCut
    apply isTotalQueryBound_bind
    · apply (isQueryBoundP_true_iff _ _).mp
      apply (RawCtxSupportedSample.sum_bound prior (fun _ => True) qPrior).mpr
      exact bounded.isQueryBoundP
    · intro context
      apply isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
      intro root
      apply (isQueryBound_map_iff _ _ _ _ _).mpr
      exact CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64
  · intro cut
    apply (isQueryBound_map_iff _ _ _ _ _).mpr
    exact cut_uniform source writer sender route decode qPost qCheck qKnown qPre qApplication qSelector qAux prior caps stage cut

end BeaconcryptCore.Computational.PqxdhInitialSourceAliasResources
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceAliasResources.step_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceAliasResources.step_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceAliasResources.program_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceAliasResources.program_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceAliasResources.client_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceAliasResources.client_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceAliasResources.cut_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceAliasResources.cut_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceAliasResources.consistent_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceAliasResources.consistent_uniform
