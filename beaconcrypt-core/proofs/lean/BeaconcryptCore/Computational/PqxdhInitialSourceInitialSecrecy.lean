import BeaconcryptCore.Computational.PqxdhInitialSourceRootErasure
import BeaconcryptCore.Computational.PqxdhInitialCurrentSecrecy

/-!
The ordinary initial Extract/HMAC comparison observes the actual complete source publication and byte-lineage freshness event. Its context precedes the independently uniform root; the executable observer receives only the supplied64-byte response, retains both actual directional chains and the complete original adaptive schedule, and runs all public HKDF evaluations as real computations.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSourceInitialSecrecy
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily PqxdhInitialBeaconAmbient
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}

structure Input (extra : OracleSpec ι) (M P I D K X Response A N : Type) (S B : Nat) where
  selectedMessage : Message
  other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
    (Ambient A N RootOracle.QueryCache)
  index : Fin S
  metadata : P
  ready : PqxdhPrivateAcceptedRoot.Ready
  post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Bool
  before : PqxdhInitialOriginPostPath.Front M P I D K S B
  selected : RawCtxProtocolReveals.Owner S B
  number : Std.U64
  ancestors : List RatchetChain
  disclosed : List RatchetChain
  shared : RawCtxSharedPrimitive.SharedState A
  privateState : N
  cache : RootOracle.QueryCache

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)

noncomputable def sourceGame (input : Input extra M P I D K X Response A N S B)
    (root : RootOutput) (response : PqxdhInitialRootLabelService.Response) (stage : Nat) : ProbComp Bool :=
  PqxdhInitialSourceExperiment.game source writer input.selectedMessage root response input.other sender route decode
    input.index input.metadata { input.ready with root := root } input.post input.before input.selected input.number input.ancestors input.disclosed
    input.shared input.privateState input.cache stage

/-- The complete original publication/freshness event consumes only the supplied64 initializer response; both appearances of the unavailable input root are erased by checked source laws. -/
theorem source_root_unused (input : Input extra M P I D K X Response A N S B)
    (left right : RootOutput) (response : PqxdhInitialRootLabelService.Response) (stage : Nat) :
    sourceGame source writer sender route decode input left response stage =
      sourceGame source writer sender route decode input right response stage := by
  unfold sourceGame
  rw [PqxdhInitialSourceRootErasure.game_ready_root_unused source writer input.selectedMessage left response input.other sender route decode
    input.index input.metadata input.ready input.post input.before input.selected input.shared input.privateState input.cache
    left input.number input.ancestors input.disclosed stage,
    PqxdhInitialSourceRootErasure.game_ready_root_unused source writer input.selectedMessage right response input.other sender route decode
      input.index input.metadata input.ready input.post input.before input.selected input.shared input.privateState input.cache
      right input.number input.ancestors input.disclosed stage]
  exact PqxdhInitialSourceRootErasure.game_root_unused source writer input.selectedMessage left right response input.other sender route decode
    input.index input.metadata input.ready input.post input.before input.selected input.shared input.privateState input.cache
    input.number input.ancestors input.disclosed stage

abbrev Context (extra : OracleSpec ι) (M P I D K X Response A N : Type) (S B : Nat) :=
  Bool ⊕ Input extra M P I D K X Response A N S B

noncomputable def observe (context : Context extra M P I D K X Response A N S B)
    (response : PqxdhInitialRootLabelService.Response) : ProbComp Bool :=
  match context with
  | .inl decision => pure decision
  | .inr input => sourceGame source writer sender route decode input (List.Vector.replicate 32 0) response 0

noncomputable def sampler (prior : ProbComp (Context extra M P I D K X Response A N S B)) :
    SecretInputSampler (Context extra M P I D K X Response A N S B) :=
  (do let context ← prior
      let root ← $ᵗ RootOutput
      pure (context, root.toList) : ProbComp (Context extra M P I D K X Response A N S B × Pqxdh.Bytes))

noncomputable def observer : FullObserver (Context extra M P I D K X Response A N S B) :=
  fun context output => observe source writer sender route decode context
    (RawCtxSelectedInitialConstructor.response64 (initialPrefix output))

noncomputable def real (prior : ProbComp (Context extra M P I D K X Response A N S B)) : ProbComp Bool := do
  let context ← prior
  let root ← $ᵗ RootOutput
  match context with
  | .inl decision => pure decision
  | .inr input => sourceGame source writer sender route decode input root (PqxdhInitialRootLabelService.realInitial source root) 0

noncomputable def random (prior : ProbComp (Context extra M P I D K X Response A N S B)) : ProbComp Bool := do
  let context ← prior
  let output ← $ᵗ HmacBlock
  observe source writer sender route decode context (RawCtxSelectedInitialConstructor.response64 output)

/-- The real full-output primitive game is the same actual source experiment and final freshness event at the independent root sampler. -/
theorem real_source (prior : ProbComp (Context extra M P I D K X Response A N S B)) :
    sourceFullGame source .ratchet (sampler prior) (observer source writer sender route decode) =
      real source writer sender route decode prior := by
  simp only [sourceFullGame, sampler, bind_assoc, pure_bind, observer,
    ← PqxdhInitialCurrentSecrecy.response_prefix, real]
  apply bind_congr
  intro context
  apply bind_congr
  intro root
  cases context with
  | inl decision => rfl
  | inr input => exact source_root_unused source writer sender route decode input _ _ _ _

/-- The complete observer sees exactly one shared uniform64 response; projecting the full76 comparison and discarding the unused root preserve the evaluated continuation distribution. -/
theorem random_source (prior : ProbComp (Context extra M P I D K X Response A N S B)) :
    𝒟[independentFullGame (sampler prior) (observer source writer sender route decode)] =
      𝒟[random source writer sender route decode prior] := by
  apply EvalDistEq.evalDist_eq
  simp only [independentFullGame, sampler, bind_assoc, pure_bind, random]
  refine EvalDistEq.bind_right prior fun context => ?_
  refine (OracleComp.EvalDistEq.bind_const ($ᵗ RootOutput)
    (do let output ← $ᵗ FullOutput; observer source writer sender route decode context output)).trans ?_
  have projected := initialPrefix_uniform.bind_left fun output =>
    observe source writer sender route decode context (RawCtxSelectedInitialConstructor.response64 output)
  simpa only [bind_map_left, observer] using projected

/-- The actual full source publication/freshness event, starting at an independent32-byte root and retaining both directions, reduces to the exact Extract sampler and ordinary HMAC PRF with coefficient one. -/
theorem bound (prior : ProbComp (Context extra M P I D K X Response A N S B))
    (hmac : HmacSha512) (correct : SourceFullCorrect source hmac) :
    (real source writer sender route decode prior).boolDistAdvantage (random source writer sender route decode prior) ≤
      (extractRealGame hmac (sampler prior) (fullExtractReduction hmac .ratchet (observer source writer sender route decode))).boolDistAdvantage
        (extractUniformGame (sampler prior) (fullExtractReduction hmac .ratchet (observer source writer sender route decode))) +
      (hmacPrfRealGame hmac (fullExpandReduction .ratchet (sampler prior) (observer source writer sender route decode))).boolDistAdvantage
        (hmacPrfRandomGame (fullExpandReduction .ratchet (sampler prior) (observer source writer sender route decode))) := by
  have randomLaw := congrArg (fun distribution : MeasureTheory.Measure Bool => distribution {true})
    (random_source source writer sender route decode prior)
  simpa only [real_source source writer sender route decode prior, ProbComp.boolDistAdvantage, randomLaw] using
    sourceFullAdvantage_le_extract_add_hmac source hmac correct .ratchet (sampler prior) (observer source writer sender route decode)

/-- The exact joint sampler pays the full original context preparation and its independent32-byte root, including common outcomes. -/
theorem sampler_uniform (prior : ProbComp (Context extra M P I D K X Response A N S B))
    (qPrior : Nat) (bounded : prior.IsTotalQueryBound qPrior) :
    (sampler prior).IsTotalQueryBound (qPrior + 32) := by
  unfold sampler
  apply isTotalQueryBound_bind bounded
  intro context
  simpa only [map_eq_bind_pure_comp, Function.comp_def, IsTotalQueryBound] using
    (isQueryBound_map_iff ($ᵗ RootOutput) (fun root => (context, root.toList)) 32 _ _).2
      (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)

end BeaconcryptCore.Computational.PqxdhInitialSourceInitialSecrecy

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceInitialSecrecy.source_root_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceInitialSecrecy.source_root_unused

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceInitialSecrecy.real_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceInitialSecrecy.real_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceInitialSecrecy.random_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceInitialSecrecy.random_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceInitialSecrecy.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceInitialSecrecy.bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceInitialSecrecy.sampler_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceInitialSecrecy.sampler_uniform
