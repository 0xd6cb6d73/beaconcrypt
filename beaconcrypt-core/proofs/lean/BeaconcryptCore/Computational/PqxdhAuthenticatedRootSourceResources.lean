import BeaconcryptCore.Computational.PqxdhAuthenticatedRootExperiment
import BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriverResources
import BeaconcryptCore.Computational.PqxdhKemCorrectnessError
import BeaconcryptCore.Computational.PqxdhAuthenticatedRootPrepareBounds

/-!
Actual source sampling costs are derived from the executed native callback programs and complete stateful continuations. Functional decapsulation means deterministic computation, including failure; it does not assert successful recovery or zero correctness error. No good-sample agreement or evaluated-distribution equality transfers a resource bound.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhAuthenticatedRootSourceResources
open PqxdhPhase2SourceAux PqxdhKemIndCca PqxdhPrivateKemSource PqxdhJointKdfGame
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPhase1AcceptanceOracle
open PqxdhInitializerSecrecy PqxdhKemCorrectnessError PqxdhChallengeSecretRouting
open PqxdhGeneratedBeaconState (IdentityHandle KemHandle)
open PqxdhPhase2JointIdentity (Converted)
variable {ι M P I D K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}

/-- The original selected decapsulation and root computation add no uniform calls; all actual local and shared-hash callback coins remain charged. -/
theorem native_auxiliary_uniform
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (functional : FunctionalDecapsulation kem)
    (secret : KemSK) (qLocal : Nat)
    (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (query : (PqxdhBeaconPhase2Publication.NativeSpec (IdentityHandle I) D (Option K) (X ⊕ Converted) Response).Domain)
    (state : SharedState A × BareState count) :
    ((PqxdhPhase2NativeSource.native source baseImpl kem secret
      (directAux attachedVerify primitives count source localImpl) query).run state).IsTotalQueryBound (max qLocal 64) := by
  rcases query with (query | (query | query)) <;> cases query <;>
    simp only [PqxdhPhase2NativeSource.native] <;>
    try exact direct_uniform_bound attachedVerify primitives count source localImpl qLocal localBound _ state
  case inl.decapsulate value key =>
    cases key with
    | some prior => exact direct_uniform_bound attachedVerify primitives count source localImpl qLocal localBound _ state
    | none => simp [functional.exact, IsTotalQueryBound]
  all_goals trivial

set_option backward.isDefEq.respectTransparency false in
/-- The actual tagged-key translation retains the same one callback cost without assuming key provenance or successful decapsulation. -/
theorem native_uniform
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (functional : FunctionalDecapsulation kem)
    (secret : KemSK) (qLocal : Nat)
    (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (query : (PqxdhPhase2PostScheduler.NativeSpec (I := I) (D := D) (K := K) (X := X) (Response := Response)).Domain)
    (state : SharedState A × BareState count) :
    ((PqxdhPhase2PostScheduler.native attachedVerify primitives count source localImpl baseImpl kem secret query).run state).IsTotalQueryBound (max qLocal 64) := by
  rcases query with (query | query)
  · cases query <;>
      simp only [PqxdhPhase2PostScheduler.native, QueryImpl.compose, PqxdhPhase2KemHandles.native,
        PqxdhPhase2KemHandles.preparation, simulateQ_spec_query]
    all_goals exact native_auxiliary_uniform attachedVerify primitives count source localImpl baseImpl kem functional secret qLocal localBound _ state
  · simp only [PqxdhPhase2PostScheduler.native, QueryImpl.compose, PqxdhPhase2KemHandles.native, simulateQ_spec_query]
    exact native_auxiliary_uniform attachedVerify primitives count source localImpl baseImpl kem functional secret qLocal localBound _ state

/-- Every actual finish attempt, including inactive and rejected calls, pays all native callbacks while preserving the original complete result and installed state. -/
theorem nativeFinish_uniform
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (functional : FunctionalDecapsulation kem)
    (secret : KemSK) (qLocal : Nat)
    (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (decode : RawCtxReceive.FrameDecoder) (query : (PqxdhPhase2LiveFinish.FinishSpec B).Domain)
    (state : PqxdhPhase2PostScheduler.State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count) :
    ((PqxdhPhase2PostScheduler.nativeFinish attachedVerify primitives count source localImpl baseImpl kem secret decode query).run state).IsTotalQueryBound (69 * max qLocal 64) := by
  cases query with
  | finish index raw =>
    simp only [PqxdhPhase2PostScheduler.nativeFinish, StateT.run, IsTotalQueryBound]
    apply (isQueryBound_map_iff _ _ _ _ _).2
    exact (isQueryBoundP_true_iff _ _).1
      (PqxdhBeaconPhase2Bounds.native_interpreted_bound
        (PqxdhPhase2PostScheduler.native attachedVerify primitives count source localImpl baseImpl kem secret)
        (fun _ => True) (max qLocal 64)
        (fun query state => (isQueryBoundP_true_iff _ _).2
          (native_uniform attachedVerify primitives count source localImpl baseImpl kem functional secret qLocal localBound query state))
        decode raw (state.1.roles.1.2 index) (state.1.primitive, state.2))

/-- The original post service may create an identity; its actual 32-byte sampler is included. -/
def postCost (qLocal uBase : Nat) : PqxdhPhase2SourceSchedulerBounds.Kind → Nat
  | .inl kind => RawCtxServerServiceBounds.uniformWeight 0 kind
  | .inr index => if index = 1 then 32 else if index = 2 then 1 else if index = 3 then uBase
      else if index = 5 then 69 * max qLocal 64 else 0

def postBill (qLocal uBase : Nat) (budget : PqxdhPhase2SourceSchedulerBounds.Budget) : Nat :=
  ∑ kind, postCost qLocal uBase kind * budget kind

set_option backward.isDefEq.respectTransparency false in
/-- Each actual postchallenge operation pays its original sampling bill, retaining the blocked public interface and unblocked private finish. -/
theorem actual_step_uniform
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (senderId : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (functional : FunctionalDecapsulation kem)
    (secret : KemSK) (challenge : MlKem768Ciphertext) (qLocal uBase : Nat)
    (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound uBase)
    (query : (PqxdhPhase2SourceScheduler.Spec baseSpec S B).Domain)
    (state : PqxdhPhase2PostScheduler.State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count) :
    ((PqxdhPhase2PostScheduler.actual attachedVerify primitives count source localImpl writer senderId route decode baseImpl kem secret challenge query).run state).IsTotalQueryBound
      (postCost qLocal uBase (PqxdhPhase2SourceSchedulerBounds.classify (baseSpec := baseSpec) query)) := by
  rcases query with ((query | query) | query)
  · have old := PqxdhProtocolQueryBounds.source_uniform_step source writer senderId route decode query state.1
    cases query <;>
      simpa [PqxdhPhase2PostScheduler.actual, StateT.run, IsTotalQueryBound, isQueryBound_map_iff,
        PqxdhPhase2SourceSchedulerBounds.classify, postCost, RawCtxRevealBudgets.weight] using old
  · rcases query with (request | ((coin | base) | ciphertext))
    · simp only [PqxdhPhase2PostScheduler.actual, borrowedSelector, StateT.run,
        PqxdhPhase2PostSource.coins, IsTotalQueryBound, isQueryBound_map_iff]
      apply (PqxdhPrivateRootQueryBounds.bare_uniform_step attachedVerify primitives count request state.2).mono
      rcases request with ((coin | query) | candidate) <;> (try cases query) <;>
        simp [PqxdhPhase2SourceSchedulerBounds.classify, postCost, PqxdhPrivatePhase1Prefix.Creating,
          PqxdhPrivateRootQueryBounds.SourceUniform, IsSourceClass, sourceQuery,
          PqxdhJointPhase1Reports.SourceClass, PqxdhDynamicIdentityPool.IsCreate, PqxdhDynamicIdentityPool.IsUniform]
    · simp [PqxdhPhase2PostScheduler.actual, borrowedSelector, StateT.run,
        PqxdhPhase2PostSource.interpretation, publicImpl,
        KEMScheme.IND_CCA_postChallengeImpl, kemAmbientImpl,
        PqxdhPhase2SourceSchedulerBounds.classify, postCost, IsTotalQueryBound]
      change OracleComp.IsTotalQueryBound (unifSpec.query coin : ProbComp _) 1
      exact (isQueryBound_query_iff (spec := unifSpec) coin 1 _ _).2 (by decide)
    · simp [PqxdhPhase2PostScheduler.actual, borrowedSelector, StateT.run,
        PqxdhPhase2PostSource.interpretation, publicImpl,
        KEMScheme.IND_CCA_postChallengeImpl, kemAmbientImpl,
        PqxdhPhase2SourceSchedulerBounds.classify, postCost, IsTotalQueryBound]
      change (simulateQ (kemAmbientImpl baseImpl) ((unifSpec + baseSpec).query (.inr base))).IsTotalQueryBound uBase
      rw [simulateQ_spec_query]
      exact baseBound base
    · simp [PqxdhPhase2PostScheduler.actual, borrowedSelector, StateT.run,
        PqxdhPhase2PostSource.interpretation, publicImpl,
        KEMScheme.IND_CCA_postChallengeImpl, kemAmbientImpl,
        PqxdhPhase2SourceSchedulerBounds.classify, postCost, IsTotalQueryBound]
      change (simulateQ (kemAmbientImpl baseImpl)
        (if ciphertext = challenge then pure none else kem.decaps secret ciphertext)).IsTotalQueryBound 0
      split <;> simp [functional.exact, IsTotalQueryBound]
  · exact nativeFinish_uniform attachedVerify primitives count source localImpl baseImpl kem functional secret qLocal localBound decode query state

/-- Every adaptive post continuation pays the sum of its actual per-class source costs on all reply branches. -/
theorem actual_post_uniform {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (senderId : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (functional : FunctionalDecapsulation kem)
    (secret : KemSK) (challenge : MlKem768Ciphertext) (qLocal uBase : Nat)
    (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound uBase)
    (client : OracleComp (PqxdhPhase2SourceScheduler.Spec baseSpec S B) Result)
    (budget : PqxdhPhase2SourceSchedulerBounds.Budget)
    (bounded : PqxdhPhase2SourceSchedulerBounds.Bounded client budget)
    (state : PqxdhPhase2PostScheduler.State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count) :
    ((simulateQ (PqxdhPhase2PostScheduler.actual attachedVerify primitives count source localImpl writer senderId route decode baseImpl kem secret challenge) client).run state).IsTotalQueryBound
      (postBill qLocal uBase budget) := by
  exact (isQueryBoundP_true_iff _ _).1
    (FinitePartitionQueryBounds.weighted_bound (PqxdhPhase2SourceSchedulerBounds.classify (baseSpec := baseSpec))
      (postCost qLocal uBase) budget
      (PqxdhPhase2PostScheduler.actual attachedVerify primitives count source localImpl writer senderId route decode baseImpl kem secret challenge)
      (fun _ => True) client bounded
      (fun query state => (isQueryBoundP_true_iff _ _).2
        (actual_step_uniform attachedVerify primitives count source localImpl writer senderId route decode baseImpl kem functional secret challenge qLocal uBase localBound baseBound query state)) state)

/-- Scalar accounting retains native record work, arbitrary source creation, public/base calls and every separate finish attempt. -/
theorem postBill_eq (qLocal uBase : Nat) (budget : PqxdhPhase2SourceSchedulerBounds.Budget) :
    postBill qLocal uBase budget = budget (.inl .coin) +
      64 * (budget (.inl .send) + budget (.inl .raw) + budget (.inl .hash)) +
      32 * budget (.inr 1) + budget (.inr 2) + uBase * budget (.inr 3) +
      69 * max qLocal 64 * budget (.inr 5) := by
  simp only [postBill, Fintype.sum_sum_type]
  have old := RawCtxServerServiceBounds.uniform_bill 0 (fun kind => budget (.inl kind))
  simp only [RawCtxServerServiceBounds.bill, Nat.zero_mul, Nat.add_zero] at old
  change (∑ kind, RawCtxServerServiceBounds.uniformWeight 0 kind * budget (.inl kind)) +
    (∑ kind : Fin 6, postCost qLocal uBase (.inr kind) * budget (.inr kind)) = _
  rw [old]
  simp [Fin.sum_univ_succ, postCost, Nat.add_assoc]

open PqxdhAuthenticatedRootExperiment PqxdhPhase2GeneratedDriver PqxdhStatefulPhase1EufCma
open PqxdhPhase2SourceSchedulerBounds (Budget Bounded ForwardedSource)
open PqxdhPrivateRootSource (Prepared)
open PqxdhPrivateAcceptedRoot (Ready)

variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (functional : FunctionalDecapsulation kem)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (qLocal uBase qAux : Nat)
    (localBound : ∀ query state, ((env.localImpl query).run state).IsTotalQueryBound qLocal)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound uBase)
    (auxBound : ∀ query state, ((env.aux query).run state).IsTotalQueryBound qAux)
    (budget : Budget) (postBound : ∀ choice response, Bounded (post choice response) budget)

include functional localBound baseBound auxBound postBound in
/-- The original accepted builder and complete actual native post execution are charged without requiring successful acceptance, good decapsulation or a security-game equality. -/
theorem nativeAccepted_uniform
    (secret : KemSK) (prepared : Prepared setup (driver env.toDriverEnvironment program).State) (ready : Ready) :
    (nativeAccepted env baseImpl kem attachedVerify primitives program post secret prepared ready).IsTotalQueryBound
      ((64 + 5 * qAux) + postBill qLocal uBase budget) := by
  apply isTotalQueryBound_bind
    (PqxdhProtocolQueryBounds.build_uniform env.source env.recordWriter env.aux qAux auxBound
      env.senderId env.index env.metadata ready prepared.1.context.selection.2)
  intro result
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using
    actual_post_uniform attachedVerify primitives 1 env.source env.localImpl env.recordWriter env.senderId env.route env.decode
      baseImpl kem functional secret ready.ciphertext qLocal uBase localBound baseBound _ budget
      (postBound prepared.1.context.selection.1 result.1) (result.2, prepared.2)

/-- Conservative ordinary interpretation cost of the common observer, including its real source creation and base work. -/
def commonUniformBill (qLocal uBase qAux : Nat) (budget : Budget) : Nat :=
  34 * PqxdhAuthenticatedRootCommonBounds.commonBill qLocal qAux budget +
    uBase * PqxdhAuthenticatedRootCommonBounds.commonBill qLocal qAux budget

include functional localBound baseBound postBound in
/-- The original unblocked completed observer retains all native/source work, even when target encapsulation or root validation fails. -/
theorem observe_uniform
    (secret : KemSK) (output : Option (PqxdhPrivateCandidateAcceptance.Outcome
      (PqxdhPrivatePhase1Prefix.Retained setup Unit (driver env.toDriverEnvironment program).State)))
    (execution : PqxdhSourceAuthenticatedRoot.ServerExecution) (state : BareState 1) :
    (evalKem baseImpl kem secret (PqxdhPrivateAcceptedRoot.observe env.source none attachedVerify primitives 1 setup
      (commonObserver env program post) output execution state)).IsTotalQueryBound (commonUniformBill qLocal uBase qAux budget) := by
  have caps := PqxdhAuthenticatedRootPrepareBounds.observe_caps env program post attachedVerify primitives
    qLocal localBound budget postBound qAux none output execution state
  simpa only [commonUniformBill, Nat.zero_mul, Nat.add_zero] using
    PqxdhPrivateRootGameBudgets.evalKem_uniform_bound baseImpl kem secret uBase 0 baseBound
      (fun ciphertext => by simp [functional.exact, IsTotalQueryBound])
      _ _ _ _ caps.uniforms caps.bases caps.decaps

include functional localBound baseBound auxBound postBound in
/-- Every accepted common candidate pays its original builder and full unblocked native/source schedule. -/
theorem acceptedObserve_uniform
    (secret : KemSK) (output : Option (PqxdhPrivateCandidateAcceptance.Outcome
      (PqxdhPrivatePhase1Prefix.Retained setup Unit (driver env.toDriverEnvironment program).State)))
    (execution : Ready) (state : BareState 1) :
    (evalKem baseImpl kem secret (PqxdhPrivateAcceptedRoot.acceptedObserve env.source none attachedVerify primitives 1 setup
      (commonObserver env program post) output execution state)).IsTotalQueryBound (commonUniformBill qLocal uBase qAux budget) := by
  have caps := PqxdhAuthenticatedRootPrepareBounds.acceptedObserve_caps env program post attachedVerify primitives
    qLocal localBound budget postBound qAux auxBound none output execution state
  simpa only [commonUniformBill, Nat.zero_mul, Nat.add_zero] using
    PqxdhPrivateRootGameBudgets.evalKem_uniform_bound baseImpl kem secret uBase 0 baseBound
      (fun ciphertext => by simp [functional.exact, IsTotalQueryBound])
      _ _ _ _ caps.uniforms caps.bases caps.decaps

/-- The real accepted and common/rejected paths keep separate complete post costs. -/
def continuationBill (qLocal uBase qAux : Nat) (budget : Budget) : Nat :=
  max (commonUniformBill qLocal uBase qAux budget) ((64 + 5 * qAux) + postBill qLocal uBase budget)

include functional localBound baseBound auxBound postBound in
/-- Actual optional encapsulation failure and every validation outcome retain their complete original continuation bill. -/
theorem nativeAfterEncapsulation_uniform
    (secret : KemSK) (prepared : Prepared setup (driver env.toDriverEnvironment program).State)
    (ephemeral : List.Vector UInt8 32) (encapsulated : Option (MlKem768Ciphertext × MlKemSharedSecret)) :
    (nativeAfterEncapsulation env baseImpl kem attachedVerify primitives program post secret prepared ephemeral encapsulated).IsTotalQueryBound
      (continuationBill qLocal uBase qAux budget) := by
  unfold nativeAfterEncapsulation
  cases encapsulated with
  | none =>
    exact (observe_uniform env baseImpl kem functional attachedVerify primitives program post qLocal uBase qAux localBound baseBound budget postBound secret _ _ _).mono (Nat.le_max_left _ _)
  | some pair =>
    rcases pair with ⟨ciphertext, shared⟩
    dsimp only
    split
    · exact (observe_uniform env baseImpl kem functional attachedVerify primitives program post qLocal uBase qAux localBound baseBound budget postBound secret _ _ _).mono (Nat.le_max_left _ _)
    · exact (nativeAccepted_uniform env baseImpl kem functional attachedVerify primitives program post qLocal uBase qAux localBound baseBound auxBound budget postBound secret prepared _).mono (Nat.le_max_right _ _)

include functional localBound baseBound auxBound postBound in
/-- Common candidates execute the actual optional native encapsulator and all rejection/acceptance branches under their original unblocked interpreter. -/
theorem allCandidateCommon_uniform
    (uEphemeral uNative : Nat)
    (ephemeralBound : (simulateQ (kemAmbientImpl baseImpl) env.ephemeralGen).IsTotalQueryBound uEphemeral)
    (nativeBound : ∀ key, (simulateQ (kemAmbientImpl baseImpl) (env.native.encaps key)).IsTotalQueryBound uNative)
    (secret : KemSK) (output : Option (PqxdhPrivateCandidateAcceptance.Outcome
      (PqxdhPrivatePhase1Prefix.Retained setup Unit (driver env.toDriverEnvironment program).State)))
    (state : BareState 1) :
    (evalKem baseImpl kem secret (PqxdhPrivateAcceptedRoot.allCandidateCommon env.source kem env.native attachedVerify primitives 1 setup
      (commonObserver env program post) output state env.server env.application env.ephemeralGen)).IsTotalQueryBound
      (uEphemeral + (uNative + commonUniformBill qLocal uBase qAux budget)) := by
  unfold PqxdhPrivateAcceptedRoot.allCandidateCommon
  cases output.bind (·.accepted) with
  | none =>
    exact (observe_uniform env baseImpl kem functional attachedVerify primitives program post qLocal uBase qAux localBound baseBound budget postBound secret _ _ _).mono (by omega)
  | some selected =>
    rcases selected with ⟨identity, keys⟩
    dsimp only
    unfold PqxdhPrivateAcceptedRoot.acceptedCommon
    split
    · exact (observe_uniform env baseImpl kem functional attachedVerify primitives program post qLocal uBase qAux localBound baseBound budget postBound secret _ _ _).mono (by omega)
    · simp only [evalKem_bind, ← PqxdhPrivateRootQueryBounds.ccaAmbient_eq_lift, evalKem_ambient]
      apply isTotalQueryBound_bind ephemeralBound
      intro ephemeral
      apply isTotalQueryBound_bind (nativeBound keys.pqKey)
      intro encapsulated
      cases encapsulated with
      | none => exact observe_uniform env baseImpl kem functional attachedVerify primitives program post qLocal uBase qAux localBound baseBound budget postBound secret _ _ _
      | some pair =>
        rcases pair with ⟨ciphertext, shared⟩
        dsimp only
        split
        · exact observe_uniform env baseImpl kem functional attachedVerify primitives program post qLocal uBase qAux localBound baseBound budget postBound secret _ _ _
        · exact acceptedObserve_uniform env baseImpl kem functional attachedVerify primitives program post qLocal uBase qAux localBound baseBound auxBound budget postBound secret _ _ _

include functional localBound baseBound auxBound postBound in
/-- The original all-candidate next action pays actual optional encapsulation before its complete native/common continuation. -/
theorem nativeNext_uniform
    (uEphemeral uNative : Nat)
    (ephemeralBound : (simulateQ (kemAmbientImpl baseImpl) env.ephemeralGen).IsTotalQueryBound uEphemeral)
    (nativeBound : ∀ key, (simulateQ (kemAmbientImpl baseImpl) (env.native.encaps key)).IsTotalQueryBound uNative)
    (secret : KemSK) (prepared : Prepared setup (driver env.toDriverEnvironment program).State) :
    (nativeNext env baseImpl kem attachedVerify primitives program post secret prepared).IsTotalQueryBound
      (uEphemeral + (uNative + continuationBill qLocal uBase qAux budget)) := by
  unfold nativeNext
  split
  · apply isTotalQueryBound_bind ephemeralBound
    intro ephemeral
    apply isTotalQueryBound_bind (nativeBound _)
    intro encapsulated
    exact nativeAfterEncapsulation_uniform env baseImpl kem functional attachedVerify primitives program post qLocal uBase qAux localBound baseBound auxBound budget postBound secret prepared ephemeral encapsulated
  · exact (allCandidateCommon_uniform env baseImpl kem functional attachedVerify primitives program post qLocal uBase qAux localBound baseBound auxBound budget postBound uEphemeral uNative ephemeralBound nativeBound secret _ _).mono (by
      exact Nat.add_le_add_left (Nat.add_le_add_left (Nat.le_max_left _ _) _) _)

include functional localBound baseBound auxBound postBound in
/-- The full original source experiment pays seed, prekey, KEM generation, one-time key, writer, enlarged prefix, optional native encapsulation and every complete later branch in their actual source order. -/
theorem actual_uniform
    (uPrekey uKeygen uOneTime uEphemeral uNative qWrite : Nat)
    (prekeyBound : ∀ identity, (simulateQ (kemAmbientImpl baseImpl) (setup.prekey identity)).IsTotalQueryBound uPrekey)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound uKeygen)
    (oneTimeBound : ∀ identity before target, (simulateQ (kemAmbientImpl baseImpl)
      (setup.oneTime identity before target)).IsTotalQueryBound uOneTime)
    (ephemeralBound : (simulateQ (kemAmbientImpl baseImpl) env.ephemeralGen).IsTotalQueryBound uEphemeral)
    (nativeBound : ∀ key, (simulateQ (kemAmbientImpl baseImpl) (env.native.encaps key)).IsTotalQueryBound uNative)
    (writerBound : ∀ fields state, ((env.phase1Writer fields).run state).IsTotalQueryBound qWrite)
    (prefixBudget : Budget) (prefixBound : ∀ reply, Bounded (program.main reply) prefixBudget)
    (noSign : ∀ reply, (program.main reply).IsQueryBoundP (ForwardedSource (baseSpec := baseSpec)
      PqxdhJointPhase1AcceptanceComposition.IsSigning) 0)
    (noCreate : ∀ reply, (program.main reply).IsQueryBoundP (ForwardedSource (baseSpec := baseSpec)
      PqxdhPrivatePhase1Prefix.Creating) 0) :
    (actual env baseImpl kem attachedVerify primitives program post).IsTotalQueryBound
      ((32 + ((uPrekey + (uKeygen + uOneTime)) +
        (2 * (qWrite + PqxdhPhase2SourceSchedulerBounds.bill qLocal prefixBudget) +
          uBase * (qWrite + PqxdhPhase2SourceSchedulerBounds.bill qLocal prefixBudget)))) +
        (uEphemeral + (uNative + continuationBill qLocal uBase qAux budget))) := by
  unfold actual PqxdhGeneratedNativeContinuation.nativeContinued
  apply isTotalQueryBound_bind
  · simpa only [Nat.zero_mul, Nat.add_zero] using
      PqxdhPhase2GeneratedDriverResources.program_uniform env.toDriverEnvironment program attachedVerify primitives 1
        baseImpl kem uBase 0 baseBound (fun secret ciphertext => by simp [functional.exact, IsTotalQueryBound])
        uPrekey uKeygen uOneTime prekeyBound keygenBound oneTimeBound qWrite writerBound qLocal localBound
        prefixBudget prefixBound noSign noCreate
  · intro stopped
    cases stopped.1 with
    | none => trivial
    | some output => exact nativeNext_uniform env baseImpl kem functional attachedVerify primitives program post qLocal uBase qAux localBound baseBound auxBound budget postBound uEphemeral uNative ephemeralBound nativeBound output.context.generated.secret _

end BeaconcryptCore.Computational.PqxdhAuthenticatedRootSourceResources

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootSourceResources.native_auxiliary_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootSourceResources.native_auxiliary_uniform
/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootSourceResources.native_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootSourceResources.native_uniform
/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootSourceResources.nativeFinish_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootSourceResources.nativeFinish_uniform
/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootSourceResources.actual_step_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootSourceResources.actual_step_uniform
/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootSourceResources.actual_post_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootSourceResources.actual_post_uniform
/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootSourceResources.postBill_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootSourceResources.postBill_eq
/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootSourceResources.nativeAccepted_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootSourceResources.nativeAccepted_uniform
/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootSourceResources.observe_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootSourceResources.observe_uniform
/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootSourceResources.acceptedObserve_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootSourceResources.acceptedObserve_uniform
/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootSourceResources.nativeAfterEncapsulation_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootSourceResources.nativeAfterEncapsulation_uniform
/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootSourceResources.allCandidateCommon_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootSourceResources.allCandidateCommon_uniform
/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootSourceResources.nativeNext_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootSourceResources.nativeNext_uniform
/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootSourceResources.actual_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootSourceResources.actual_uniform
