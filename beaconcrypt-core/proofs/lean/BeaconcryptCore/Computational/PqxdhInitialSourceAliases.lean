import BeaconcryptCore.Computational.PqxdhInitialSourceAliasCompiler
import BeaconcryptCore.Computational.PqxdhInitialAliasEvent
import BeaconcryptCore.Computational.PqxdhInitialSourceSampled
import BeaconcryptCore.Computational.RawCtxSupportedSample

/-!
The full source publication and freshness observation admits a value-consistent private initializer. The actual source client is reconstructed from the original callbacks and complete source state. The comparison samples one independent earlier root and charges every possible initializer attempt, including the first shared response. The admissibility facts below concern only the source callback implementation and initial cache, and are proved separately for actual preparation.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialSourceAliases
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhInitialSourceInitialSecrecy
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}
local notation "SourceInput" => Input extra M P I D K X Response A N S B
local notation "SourceContext" => Context extra M P I D K X Response A N S B

noncomputable def plain (input : SourceInput) : QueryImpl
    (PqxdhInitialSourceAliasCompiler.External (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response))
    (PqxdhInitialSourceAliasCompiler.Plain A N) :=
  fun query state => Prod.fst <$> ((input.other query).run state).run ∅

structure Admissible (input : SourceInput) : Prop where
  empty : input.cache = ∅
  cacheFree : input.other = PqxdhInitialSourceAliasCompiler.plainExternal (plain input)

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)

abbrev Result (M P I D K A N : Type) (S B : Nat) :=
  Option ((Bool × PqxdhInitialOriginPostPath.Snapshot M P I D K S B) × PqxdhInitialSourceAliasCompiler.LocalState A N)

noncomputable def selected (context : SourceContext) : Message :=
  match context with | .inl _ => List.Vector.replicate 128 0 | .inr input => input.selectedMessage

noncomputable def client (stage : Nat) (context : SourceContext) : OracleComp PqxdhInitialLabelCompiler.Spec (Result M P I D K A N S B) :=
  match context with
  | .inl _ => pure none
  | .inr input => some <$> PqxdhInitialSourceAliasCompiler.client source writer stage (plain input) input.selectedMessage sender route decode
      input.index input.metadata {input.ready with root := zeroRoot} input.post input.before input.selected input.shared input.privateState

noncomputable def event (context : SourceContext) (output : HmacBlock)
    (result : Result M P I D K A N S B × RootOracle.QueryCache) : Bool :=
  match context with
  | .inl decision => decision
  | .inr input => match result.1 with
    | none => false
    | some result' => PqxdhInitialSourceAliasCompiler.observation source input.selected
        (RawCtxSelectedInitialConstructor.response64 output) input.number input.ancestors input.disclosed (result', result.2)

/-- The actual complete source event is retained by the compiled client; admissibility is only a callback/cache implementation fact. -/
theorem point_source (stage : Nat) (input : SourceInput) (valid : Admissible input) (output : HmacBlock) :
    event source (.inr input) output <$>
      (simulateQ (PqxdhInitialRootLabelService.labelledFull source (QueryImpl.ofLift unifSpec ProbComp)
        input.selectedMessage (RawCtxSelectedInitialConstructor.response64 output))
        (client source writer sender route decode stage (.inr input))).run ∅ =
    sourceGame source writer sender route decode input zeroRoot (RawCtxSelectedInitialConstructor.response64 output) stage := by
  simp only [client, simulateQ_map, StateT.run_map, Functor.map_map]
  change PqxdhInitialSourceAliasCompiler.observation source input.selected
    (RawCtxSelectedInitialConstructor.response64 output) input.number input.ancestors input.disclosed <$> _ = _
  rw [PqxdhInitialSourceAliasCompiler.observed_source]
  simp only [sourceGame, valid.cacheFree, valid.empty]

/-- The actual bounded suffix gives the private initializer allowance, counting the first shared response and every compiled callback. -/
theorem client_initial (stage : Nat) (input : SourceInput) (qPost : Nat)
    (bounded : ∀ reply, (input.post reply).IsTotalQueryBound qPost) :
    (client source writer sender route decode stage (.inr input)).IsQueryBoundP
      PqxdhInitialRootAliases.IsInitializer (1 + (7 + qPost * 67)) := by
  apply (isQueryBoundP_map_iff _ _ _).2
  apply (isQueryBoundP_congr_pred (p := PqxdhInitialRootAliases.IsInitializer)
    (p' := PqxdhInitialObserverCallbackBudgets.IsService) (fun query => by
      cases query <;> simp [PqxdhInitialRootAliases.IsInitializer, PqxdhInitialObserverCallbackBudgets.IsService])).mpr
  exact PqxdhInitialSourceAliasCompiler.client_initial source writer stage (plain input) input.selectedMessage sender route decode
    input.index input.metadata {input.ready with root := zeroRoot} input.post input.before input.selected input.shared input.privateState qPost bounded

abbrev Pending (prior : ProbComp SourceContext) := RawCtxSupportedSample.Pending prior

noncomputable def erase (prior : ProbComp SourceContext) (context : Bool ⊕ Pending prior) : SourceContext :=
  Sum.map id Subtype.val context

noncomputable def consistent (prior : ProbComp SourceContext) (stage : Nat) : ProbComp Bool :=
  PqxdhInitialAliasEvent.rightGame source (fun context => selected (erase prior context))
    (fun context => client source writer sender route decode stage (erase prior context))
    (fun context => event source (erase prior context)) (RawCtxSupportedSample.sum prior)

/-- Forward support certificates preserve the whole original source sampler and every original final event. -/
theorem sampled_source (prior : ProbComp SourceContext) (stage : Nat)
    (valid : ∀ input, Sum.inr input ∈ support prior → Admissible input) :
    PqxdhInitialAliasEvent.sourceGame source (fun context => selected (erase prior context))
      (fun context => client source writer sender route decode stage (erase prior context))
      (fun context => event source (erase prior context)) (RawCtxSupportedSample.sum prior) =
    PqxdhInitialSourceSampled.game source writer sender route decode prior stage := by
  unfold PqxdhInitialAliasEvent.sourceGame
  have point : ∀ context : Bool ⊕ Pending prior, ∀ output : HmacBlock,
      event source (erase prior context) output <$>
        (simulateQ (PqxdhInitialRootLabelService.labelledFull source (QueryImpl.ofLift unifSpec ProbComp)
          (selected (erase prior context)) (RawCtxSelectedInitialConstructor.response64 output))
          (client source writer sender route decode stage (erase prior context))).run ∅ =
        PqxdhInitialSourceSampled.observe source writer sender route decode (erase prior context)
          (RawCtxSelectedInitialConstructor.response64 output) stage := by
    intro context output
    cases context with
    | inl decision => rfl
    | inr input => exact point_source source writer sender route decode stage input.val (valid input.val input.property) output
  simp_rw [point]
  exact RawCtxSupportedSample.sum_run prior (fun context => do
    let output ← $ᵗ HmacBlock
    PqxdhInitialSourceSampled.observe source writer sender route decode context (RawCtxSelectedInitialConstructor.response64 output) stage)

/-- The complete selected source event, at any evolving-chain stage, differs from value-consistent private initialization only by the explicit independent-root collision allowance. -/
theorem bound (prior : ProbComp SourceContext) (stage qPost : Nat)
    (valid : ∀ input, Sum.inr input ∈ support prior → Admissible input)
    (bounded : ∀ input, Sum.inr input ∈ support prior → ∀ reply, (input.post reply).IsTotalQueryBound qPost) :
    (PqxdhInitialSourceSampled.game source writer sender route decode prior stage).boolDistAdvantage
      (consistent source writer sender route decode prior stage) ≤
      ((1 + (7 + qPost * 67) : Nat) : ENNReal).toReal / (2 ^ 256 : ℝ) := by
  have result := PqxdhInitialAliasEvent.bound source (fun context => selected (erase prior context))
    (fun context => client source writer sender route decode stage (erase prior context))
    (fun context => event source (erase prior context)) (RawCtxSupportedSample.sum prior) (1 + (7 + qPost * 67))
    (fun context => by
      cases context with
      | inl decision => trivial
      | inr input => exact client_initial source writer sender route decode stage input.val qPost (bounded input.val input.property))
  rw [sampled_source source writer sender route decode prior stage valid] at result
  simpa only [consistent, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_ofNat] using result

end BeaconcryptCore.Computational.PqxdhInitialSourceAliases

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceAliases.point_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceAliases.point_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceAliases.client_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceAliases.client_initial

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceAliases.sampled_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceAliases.sampled_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceAliases.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceAliases.bound
