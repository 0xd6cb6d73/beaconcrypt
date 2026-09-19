import BeaconcryptCore.Computational.PqxdhInitialObserverCallbackBudgets
import BeaconcryptCore.Computational.PqxdhInitialBuilderQueryBounds
import BeaconcryptCore.Computational.PqxdhInitialObserverBudgets

/-!
The actual Server builder can request its private response-only initializer at most once. The proof follows its original admission, identity and reservation gates and preserves all later arbitrary native replies. Ordinary sampling and callback interpreters have no initializer capability, so the bound does not depend on their runtime or infer a source cap from a distribution equality.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialBuilderServiceBound
open PqxdhServerRegistrationPublication PqxdhInitialServiceBuilder PqxdhInitialResponseService
open PqxdhJointKdfGame PqxdhSecretInputKdf
variable {ι Result : Type} {base : OracleSpec ι}

def Initial : (PqxdhInitialResponseService.Spec base).Domain → Prop
  | .inr _ => True
  | _ => False
instance : DecidablePred (Initial (base := base)) :=
  fun query => by cases query <;> simp only [Initial] <;> infer_instance

private theorem original_bound (client : OracleComp base Result) :
    (simulateQ original client).IsQueryBoundP (Initial (base := base)) 0 := by
  apply RawCtxSourceOpen.simulate_bound original (fun _ => False) Initial client 0 (isQueryBoundP_false client 0)
  intro query
  exact (isQueryBoundP_query_iff (spec := PqxdhInitialResponseService.Spec base) (p := Initial) (.inl query) 0).mpr
    (by simp [Initial])

set_option backward.isDefEq.respectTransparency false in
/-- After the actual identity and reservation gates, the candidate builder issues one initializer and no later operation can repeat it. -/
theorem candidate_initial {Metadata PeerMetadata Consumed : Type}
    (pending : pqxdh.ServerRegistrationCandidate) (root : RootOutput) (data : Option Bytes)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) :
    (candidate pending root data metadata state).IsQueryBoundP (Initial (base := TailSpec)) 1 := by
  simp only [candidate, original, isQueryBoundP_query_bind_iff, Initial,
    not_false_eq_true, true_or, if_false, true_and]
  intro valid
  cases valid
  · simp only [Bool.not_false, if_true]
    trivial
  · simp only [Bool.not_true, Bool.false_eq_true, if_false,
      isQueryBoundP_query_bind_iff, Initial, not_false_eq_true, true_or, true_and]
    intro reserved
    cases reserved
    · simp only [Bool.not_false, if_true]
      trivial
    · simp only [Bool.not_true, Bool.false_eq_true, if_false, kernel, initial,
        bind_assoc, pure_bind, isQueryBoundP_query_bind_iff, Initial, not_true_eq_false,
        false_or, if_true]
      exact ⟨by decide, fun response => original_bound _⟩

/-- All current allocation and consumed-binding checks precede the same at-most-one initializer site. -/
theorem used_initial {Metadata PeerMetadata Consumed : Type}
    (pending : PqxdhRegistrationInputs.UsedInput) (root : RootOutput) (data : Option Bytes)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) :
    (usedBuild pending root data metadata state).IsQueryBoundP (Initial (base := TailSpec)) 1 := by
  apply PqxdhInitialBuilderQueryBounds.continue_bound
  rintro (_ | next)
  all_goals try exact isQueryBoundP_pure _ _ _
  apply PqxdhInitialBuilderQueryBounds.continue_bound
  rintro (prepared | _)
  all_goals first | exact candidate_initial _ root data metadata state | exact isQueryBoundP_pure _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Every ordinary native builder callback retains its complete coins and shared effects without initializer access; the single service callback forwards once. -/
theorem tail_initial {A : Type} (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (query : BuilderSpec.Domain) (state : RawCtxSharedPrimitive.SharedState A) :
    ((tailImpl fixed writer aux query).run state).IsQueryBoundP (Initial (base := unifSpec))
      (if Initial (base := TailSpec) query then 1 else 0) := by
  cases query with
  | inl query => exact original_bound _
  | inr request =>
      simp only [tailImpl, StateT.run, initial, isQueryBoundP_query_bind_iff, Initial, if_true]
      exact ⟨by decide, fun _ => isQueryBoundP_pure _ _ _⟩

/-- Source role reinstallation adds no initializer calls to the actual at-most-one builder site. -/
theorem protocol_initial {M P I D K A : Type} {S B : Nat}
    (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (sender : M → Std.U64) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (state : PqxdhRegistrationProtocolState.State M P I D K A S B) :
    ((protocolBuild fixed writer aux sender index metadata ready).run state).IsQueryBoundP (Initial (base := unifSpec)) 1 := by
  simp only [protocolBuild, StateT.run, isQueryBoundP_map_iff]
  exact (used_initial _ _ _ _ _).simulateQ_run_StateT_of_step (tail_initial fixed writer aux) _

set_option backward.isDefEq.respectTransparency false in
/-- Compiling the actual builder's initializer label preserves the same service count and forwards all ordinary coins. -/
theorem compiler_initial (selected : PqxdhCorrelatedExtractFamily.Message)
    (client : OracleComp RunSpec Result) (count : Nat)
    (bounded : client.IsQueryBoundP (Initial (base := unifSpec)) count) :
    (simulateQ (PqxdhInitialLabelBuilder.compiler selected) client).IsQueryBoundP
      PqxdhInitialObserverCallbackBudgets.IsService count := by
  apply RawCtxSourceOpen.simulate_bound _ (Initial (base := unifSpec)) _ client count bounded
  intro query
  cases query <;> simp only [PqxdhInitialLabelBuilder.compiler, isQueryBoundP_query_iff,
    PqxdhInitialObserverCallbackBudgets.IsService, Initial, if_true, if_false] <;> decide

/-- The complete labelled Server builder consumes at most one private initializer query, independently of all primitive and local callback coins. -/
theorem build_initial {M P I D K A : Type} {S B : Nat}
    (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (sender : M → Std.U64) (index : Fin S) (metadata : P) (selected : PqxdhCorrelatedExtractFamily.Message)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (state : PqxdhRegistrationProtocolState.State M P I D K A S B) :
    (PqxdhInitialLabelBuilder.build fixed writer aux sender index metadata selected ready state).IsQueryBoundP
      PqxdhInitialObserverCallbackBudgets.IsService 1 :=
  compiler_initial selected _ 1 (protocol_initial fixed writer aux sender index metadata _ state)

set_option backward.isDefEq.respectTransparency false in
/-- The actual accepted current observer issues at most the one Server initializer plus one service request per permitted post finish. -/
theorem accepted_initial {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
    {setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : PqxdhEd25519EufCma.Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : PqxdhJointIdentity.Primitives)
    (program : PqxdhPhase2GeneratedDriver.Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (c : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program post)
    (secret : KemSK) (selected : PqxdhCorrelatedExtractFamily.Message)
    (prepared : PqxdhPrivateRootSource.Prepared setup
      (PqxdhPhase2GeneratedDriver.driver env.toDriverEnvironment program).State)
    (ready : PqxdhPrivateAcceptedRoot.Ready) :
    (PqxdhInitialLegalObserver.accepted env baseImpl kem attachedVerify primitives program post secret selected prepared ready).IsQueryBoundP
      PqxdhInitialObserverCallbackBudgets.IsService (1 + c.privatePost) := by
  unfold PqxdhInitialLegalObserver.accepted
  apply isQueryBoundP_bind (build_initial _ _ _ _ _ _ _ _ _)
  intro result _supported
  rw [isQueryBoundP_map_iff]
  exact (c.postBound prepared.1.context.selection.1 result.1 (.inr 5)).simulateQ_run_StateT_of_step
    (PqxdhInitialObserverBudgets.target_service attachedVerify primitives 1 env.source env.localImpl
      env.recordWriter env.senderId env.route env.decode baseImpl kem secret ready.ciphertext) _

end BeaconcryptCore.Computational.PqxdhInitialBuilderServiceBound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderServiceBound.candidate_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderServiceBound.candidate_initial
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderServiceBound.used_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderServiceBound.used_initial

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderServiceBound.tail_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderServiceBound.tail_initial

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderServiceBound.protocol_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderServiceBound.protocol_initial

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderServiceBound.compiler_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderServiceBound.compiler_initial
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderServiceBound.build_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderServiceBound.build_initial

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderServiceBound.accepted_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderServiceBound.accepted_initial
