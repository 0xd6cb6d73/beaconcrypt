-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRelatedRoot
import BeaconcryptCore.Computational.RegistrationServerRootCompiler

/-! Private source interpretation of the native root interface after dropping only its analysis history/cache. This is an exact source evaluation, not an adversary capability: selected seed and prekey scalar remain private parameters. Legacy Server descriptors use the proved additive embedding. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSourceRoot
open PqxdhSecretInputKdf (HmacSha512 SourceRootCorrect RootOutput)
open PqxdhJointIdentity (Primitives IdentitySeed)
open PqxdhJointGapDh (DhInterface ScalarBytes)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open RegistrationNativeRelatedFamily (Message State input)
open RegistrationNativeRelatedRoot (RootSpec)
variable {Value : Type}

def value (source : FixedHkdfSha512NoSaltSource) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (message : Message) : Option RootOutput :=
  (input joint dh seed scalar message).map (RegistrationNativeRelatedRoot.nativeRoot source)

def handler (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes) :
    QueryImpl RootSpec ProbComp
  | .inl coin => unifSpec.query coin
  | .inr (.sign bytes) => pure (joint.sign seed bytes)
  | .inr (.publicHmac key bytes) => pure (hmac.eval key bytes)
  | .inr (.derive message) => pure (value source joint dh seed scalar message)

/-- Every actual native source-root reply is independent only of the private analysis history/cache; selected secret evaluation remains on the private side. -/
theorem query_value (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (query : RootSpec.Domain) (before : State) :
    Prod.fst <$> (RegistrationNativeRelatedRoot.sourceImpl source hmac joint dh seed scalar query).run before =
      handler source hmac joint dh seed scalar query := by
  cases query with
  | inl coin =>
      simp only [RegistrationNativeRelatedRoot.sourceImpl, RegistrationNativeRelatedFamily.realImpl,
        RegistrationNativeRelatedFamily.impl, StateT.run, handler, map_bind, map_pure]
      exact bind_pure _
  | inr request =>
      cases request with
      | sign bytes => rfl
      | publicHmac key bytes => rfl
      | derive message =>
          simp only [RegistrationNativeRelatedRoot.sourceImpl, RegistrationNativeRelatedRoot.sourceRoot,
            StateT.run, handler, value]
          cases input joint dh seed scalar message <;> rfl

private theorem discard_state {Index Private : Type} {spec : OracleSpec Index}
    (stateful : QueryImpl spec (StateT Private ProbComp)) (stateless : QueryImpl spec ProbComp)
    (step : ∀ query before, Prod.fst <$> (stateful query).run before = stateless query)
    (work : OracleComp spec Value) (before : Private) :
    Prod.fst <$> (simulateQ stateful work).run before = simulateQ stateless work := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure output => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      calc
        _ = (stateful query).run before >>=
            fun reached => simulateQ (stateless) (next reached.1) := by
          apply bind_congr
          intro reached
          exact ih reached.1 reached.2
        _ = (Prod.fst <$>
            (stateful query).run before) >>=
              fun reply => simulateQ (stateless) (next reply) := by
          rw [bind_map_left]
        _ = _ := by rw [step]

/-- Complete adaptive native-root source clients retain their exact outputs when only inaccessible analysis state is discarded. -/
theorem program_value (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (work : OracleComp RootSpec Value) (before : State) :
    Prod.fst <$>
        (simulateQ (RegistrationNativeRelatedRoot.sourceImpl source hmac joint dh seed scalar) work).run before =
      simulateQ (handler source hmac joint dh seed scalar) work :=
  discard_state _ _ (query_value source hmac joint dh seed scalar) work before

/-- Actual legacy Server root replies embed into the same private native source evaluator, independently of legacy instrumentation state. -/
theorem legacy_query (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : SourceRootCorrect source hmac) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (query : PqxdhJointDhExtractRoot.RootSpec.Domain) (before : PqxdhJointDhExtractFamily.State) :
    Prod.fst <$> (RegistrationServerRootCompiler.family hmac joint dh seed scalar query).run before =
      simulateQ (handler source hmac joint dh seed scalar) (RegistrationNativeRelatedRoot.legacy query) := by
  rw [RegistrationServerRootCompiler.family,
    PqxdhJointDhExtractRoot.reduction_step source hmac correct]
  cases query with
  | inl coin =>
      simp only [PqxdhJointDhExtractRoot.sourceImpl, PqxdhJointDhExtractFamily.realImpl,
        PqxdhJointDhExtractFamily.impl, StateT.run, RegistrationNativeRelatedRoot.legacy,
        simulateQ_spec_query, handler, map_bind, map_pure]
      exact bind_pure _
  | inr request =>
      cases request with
      | sign bytes => simp [PqxdhJointDhExtractRoot.sourceImpl, RegistrationNativeRelatedRoot.legacy,
          handler, PqxdhJointDhExtractFamily.realImpl]; rfl
      | publicHmac key bytes => simp [PqxdhJointDhExtractRoot.sourceImpl, RegistrationNativeRelatedRoot.legacy,
          handler, PqxdhJointDhExtractFamily.realImpl]; rfl
      | derive message =>
          simp only [PqxdhJointDhExtractRoot.sourceImpl, PqxdhJointDhExtractRoot.sourceRoot,
            RegistrationNativeRelatedRoot.legacy, simulateQ_spec_query, handler, value,
            RegistrationNativeRelatedFamily.input_ofLegacy, StateT.run]
          cases PqxdhJointDhExtractFamily.input joint dh seed scalar message <;> rfl

/-- Every legacy Server source-root continuation uses the same native private source evaluator after the additive message embedding. -/
theorem legacy_program (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : SourceRootCorrect source hmac) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (work : OracleComp PqxdhJointDhExtractRoot.RootSpec Value) (before : PqxdhJointDhExtractFamily.State) :
    Prod.fst <$> (simulateQ (RegistrationServerRootCompiler.family hmac joint dh seed scalar) work).run before =
      simulateQ (handler source hmac joint dh seed scalar)
        (simulateQ RegistrationNativeRelatedRoot.legacy work) := by
  rw [← QueryImpl.simulateQ_compose]
  exact discard_state _ _ (legacy_query source hmac correct joint dh seed scalar) work before

/-- A stateful legacy Server source program keeps its entire local poststate while only the private family instrumentation is erased. -/
theorem interpret_value {Local Value : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : SourceRootCorrect source hmac) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (work : StateT Local (OracleComp PqxdhJointDhExtractRoot.RootSpec) Value)
    (before : PqxdhJointDhExtractFamily.State × Local) :
    Prod.map id Prod.snd <$>
        (RegistrationServerRootCompiler.interpret (RegistrationServerRootCompiler.family hmac joint dh seed scalar) work).run before =
      simulateQ (handler source hmac joint dh seed scalar)
        (simulateQ RegistrationNativeRelatedRoot.legacy (work.run before.2)) := by
  simpa only [RegistrationServerRootCompiler.interpret, StateT.run, Functor.map_map, Prod.map, id_eq] using
    legacy_program source hmac correct joint dh seed scalar (work.run before.2) before.1

end BeaconcryptCore.Computational.RegistrationNativeSourceRoot

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceRoot.query_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceRoot.query_value
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceRoot.program_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceRoot.program_value
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceRoot.legacy_query' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceRoot.legacy_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceRoot.legacy_program' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceRoot.legacy_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceRoot.interpret_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceRoot.interpret_value
