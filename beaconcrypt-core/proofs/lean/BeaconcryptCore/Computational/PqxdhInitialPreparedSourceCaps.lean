import BeaconcryptCore.Computational.PqxdhInitialPreparedSourceInput
import BeaconcryptCore.Computational.PqxdhInitialSampledResources
import BeaconcryptCore.Computational.FinitePartitionTotal
import BeaconcryptCore.Computational.PqxdhPhase2SourceHistory

/-!
The actual authenticated preparation supplies the finite source caps used by evolving-chain reductions. The certificate budgets original callbacks and caller requests. This consumer interprets their concrete base/decapsulation/coin costs and retains the original preparation history, rather than assuming a whole-observer resource bound.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialPreparedSourceCaps
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhInitialBeaconAmbient PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity
open PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver PqxdhAuthenticatedRootExperiment
open PqxdhPhase1AcceptanceOracle PqxdhPrivateKemSource PqxdhGeneratedBeaconState
open PqxdhInitialPreparedSourceInput PqxdhInitialSourcePreparedSecrecy
open PqxdhChallengeSecretRouting PqxdhChallengeSecretQueryBounds
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (c : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program post)

def preCap : Nat := FinitePartitionQueryBounds.bill (fun _ => 1) c.preBudget
def knownCap (disclosed : List RatchetChain) : Nat := disclosed.length + env.initial.roles.2.observations.length + preCap env baseImpl kem program post c

def postCap : Nat := FinitePartitionQueryBounds.bill (fun _ => 1) c.postBudget
def callbackCap : Nat := max c.qLocal 64 + c.qDecap
def selectorCap : Nat := 34 + c.qBase + c.qDecap

/-- Every original post request is charged once in the complete finite source partition. -/
theorem post_total (choice : program.Selection) (reply : RustM (Option PqxdhServerRegistrationPublication.Response)) :
    (post choice reply).IsTotalQueryBound (postCap env baseImpl kem program post c) :=
  FinitePartitionTotal.bound PqxdhPhase2SourceSchedulerBounds.classify (post choice reply) c.postBudget (c.postBound choice reply)

/-- Interpreting the original preparation/application callback charges its real local work and every permitted selected-key decapsulation. -/
theorem interpreted_callback (secret : KemSK) (challenge : MlKem768Ciphertext)
    (query : (PqxdhInitialRootFreeCallbacks.ActualBaseSpec I (DhPair setup) K X Response).Domain)
    (state : RawCtxSharedPrimitive.SharedState A × BareState 1) :
    ((PqxdhInitialRootFreeCallbacks.interpreted attachedVerify primitives 1 env.source env.localImpl baseImpl kem secret challenge query).run state).IsTotalQueryBound
      (callbackCap env baseImpl kem program post c) := by
  have original := PqxdhInitialObserverCallbackBudgets.work_caps (baseSpec := baseSpec) attachedVerify primitives 1 env.source env.localImpl
    c.qLocal c.localBound challenge query state
  have counted := PqxdhInitialObserverCallbackBudgets.public_uniform baseImpl kem secret challenge
    c.qBase c.qDecap c.baseBound (c.decapsBound secret) _ (max c.qLocal 64) 0 1 original.1 original.2.1
    (original.2.2.mono (by split <;> omega))
  simpa only [PqxdhInitialRootFreeCallbacks.interpreted, StateT.run, Nat.mul_zero, Nat.add_zero, Nat.mul_one, callbackCap] using counted

/-- A forwarded selector retains identity-creation coins, ordinary public coins, base work and blocked-challenge decapsulation costs. The later schedule has no implicit no-creation restriction. -/
theorem selector_uniform (secret : KemSK) (challenge : MlKem768Ciphertext)
    (query : (SelectorSpec baseSpec).Domain) (state : BareState 1) (cache : RootOracle.QueryCache) :
    (((PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem secret challenge query).run state).run cache).IsTotalQueryBound
      (selectorCap env baseImpl kem program post c) := by
  have uniforms := (PqxdhPrivateRootQueryBounds.borrowed_uniform_step (baseSpec := baseSpec) attachedVerify primitives 1 query state).mono
    (show _ ≤ 34 by split_ifs <;> omega)
  have bases := (PqxdhPrivateRootQueryBounds.borrowed_class_step (baseSpec := baseSpec) attachedVerify primitives 1
    IsMlKemBaseQuery (fun coin => by simp [IsMlKemBaseQuery]) query state).mono (show _ ≤ 1 by split_ifs <;> omega)
  have decaps := (PqxdhPrivateRootQueryBounds.borrowed_class_step (baseSpec := baseSpec) attachedVerify primitives 1
    IsMlKemLogicalDecapsulationQuery (fun coin => by simp [IsMlKemLogicalDecapsulationQuery]) query state).mono
    (show _ ≤ 1 by split_ifs <;> omega)
  have counted := PqxdhInitialObserverCallbackBudgets.public_uniform baseImpl kem secret challenge
    c.qBase c.qDecap c.baseBound (c.decapsBound secret) _ 34 1 1
    (PqxdhPhase2PostSchedulerBounds.publicWork_bound .uniform _ 34 uniforms)
    (PqxdhPhase2PostSchedulerBounds.publicWork_bound .base _ 1 bases)
    (PqxdhPhase2PostSchedulerBounds.publicWork_bound .decapsulation _ 1 decaps)
  simpa only [PqxdhInitialPendingCurrent.selector, StateT.run, IsTotalQueryBound, isQueryBound_map_iff, selectorCap, Nat.mul_one] using counted

/-- All four actual source callback categories expose concrete finite costs; the initializer is handled by its separate exact32-byte source service. -/
theorem callbacks (secret : KemSK) (challenge : MlKem768Ciphertext) :
    (∀ query state cache, (pre (other env baseImpl kem attachedVerify primitives secret challenge) query state cache).IsTotalQueryBound
      (callbackCap env baseImpl kem program post c)) ∧
    (∀ query state cache, (application (other env baseImpl kem attachedVerify primitives secret challenge) query state cache).IsTotalQueryBound
      (callbackCap env baseImpl kem program post c)) ∧
    (∀ query state cache, (selector (other env baseImpl kem attachedVerify primitives secret challenge) query state cache).IsTotalQueryBound
      (selectorCap env baseImpl kem program post c)) ∧
    (∀ query state cache, (aux (other env baseImpl kem attachedVerify primitives secret challenge) query state cache).IsTotalQueryBound c.qAux) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro query state cache
    exact (isQueryBound_map_iff _ _ _ _ _).2 (interpreted_callback env baseImpl kem attachedVerify primitives program post c secret challenge (.inl query) state)
  · intro reply state cache
    exact (isQueryBound_map_iff _ _ _ _ _).2 (interpreted_callback env baseImpl kem attachedVerify primitives program post c secret challenge (.inr (.inr reply)) state)
  · intro query state cache
    change ((fun result => ((result.1.1, (state.1, result.1.2)), result.2)) <$>
      (((PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem secret challenge query).run state.2).run cache)).IsTotalQueryBound _
    exact (isQueryBound_map_iff _ _ _ _ _).2
      (selector_uniform env baseImpl kem attachedVerify primitives program post c secret challenge query state.2 cache)
  · intro query state cache
    exact (isQueryBound_map_iff _ _ _ _ _).2 (c.auxBound query state.1)

/-- A pending root dispatch retains precisely its original prepared source state; all abort and non-target paths finish instead. -/
theorem dispatch_pending (secret : KemSK)
    (prepared found : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State)
    (ephemeral : List.Vector UInt8 32)
    (supported : PqxdhPrivateRootSource.Mode.pending found ephemeral ∈ support
      (evalKem baseImpl kem secret (PqxdhPrivateAcceptedRoot.dispatch kem env.parameters attachedVerify primitives setup
        (commonObserver env program post) prepared))) : found = prepared := by
  unfold PqxdhPrivateAcceptedRoot.dispatch at supported
  split at supported
  · simp only [evalKem, simulateQ_pure, mem_support_pure_iff] at supported
    cases supported
  · split at supported
    · simp only [evalKem_bind, mem_support_bind_iff] at supported
      obtain ⟨actual, _, tail⟩ := supported
      split at tail
      · simp only [evalKem, simulateQ_pure, mem_support_pure_iff] at tail
        cases tail
        rfl
      · simp only [evalKem, simulateQ_bind, simulateQ_pure, mem_support_bind_iff, mem_support_pure_iff] at tail
        obtain ⟨_, _, _, _, impossible⟩ := tail
        cases impossible
    · simp only [evalKem, simulateQ_bind, simulateQ_pure, mem_support_bind_iff, mem_support_pure_iff] at supported
      obtain ⟨_, _, impossible⟩ := supported
      cases impossible

/-- The actual evaluated generated-prefix state retains at most the original initial observations plus the complete prechallenge source request allowance. -/
theorem prefix_history (secret : KemSK) (key : TargetKemPublicKey)
    (prepared : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State)
    (supported : prepared ∈ support (evalKem baseImpl kem secret
      (PqxdhGeneratedRootSource.borrowedPrefix attachedVerify primitives setup (driver env.toDriverEnvironment program) key))) :
    prepared.1.context.selection.2.roles.2.observations.length ≤
      env.initial.roles.2.observations.length + preCap env baseImpl kem program post c := by
  rw [PqxdhGeneratedRootSource.borrowedPrefix_evaluated] at supported
  simp only [mem_support_bind_iff] at supported
  obtain ⟨seed, _, before, _, after, _, selected, reached, finished⟩ := supported
  obtain rfl := eq_of_mem_support_pure _ finished
  rw [PqxdhPhase2GeneratedDriver.driver_private] at reached
  simp only [evalKem, simulateQ_map, support_map] at reached
  obtain ⟨actual, actualSupport, rfl⟩ := reached
  have length := PqxdhPhase2SourceHistory.driver_length attachedVerify primitives 1 baseImpl kem secret
    env.toDriverEnvironment program (preCap env baseImpl kem program post c)
    (fun reply => FinitePartitionTotal.bound PqxdhPhase2SourceSchedulerBounds.classify (program.main reply) c.preBudget (c.preBound reply))
    _ _ _ _ _ actual actualSupport
  simpa only [PqxdhPhase2GeneratedDriver.unpackSelection, PqxdhPhase2OldSource.unpackState] using length

/-- The actual preparation sampler's pending state comes from its same generated source prefix; dispatch cannot replace the retained history. -/
theorem prepared_history
    (context : PqxdhInitialLegalObserver.Context env kem attachedVerify primitives program post)
    (supported : context ∈ support (PqxdhCorrelatedExtractFamily.prepare baseImpl kem
      (protocol env kem attachedVerify primitives program post)))
    (prepared : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State)
    (ephemeral : List.Vector UInt8 32) (pending : context.state = .pending prepared ephemeral) :
    prepared.1.context.selection.2.roles.2.observations.length ≤
      env.initial.roles.2.observations.length + preCap env baseImpl kem program post c := by
  simp only [PqxdhCorrelatedExtractFamily.prepare, mem_support_bind_iff] at supported
  obtain ⟨keys, _, mode, modeSupport, pair, _, finished⟩ := supported
  obtain rfl := eq_of_mem_support_pure _ finished
  change mode = .pending prepared ephemeral at pending
  subst mode
  change PqxdhPrivateRootSource.Mode.pending prepared ephemeral ∈ support
    (evalKem baseImpl kem keys.2 ((protocol env kem attachedVerify primitives program post).prepare keys.1)) at modeSupport
  simp only [protocol, evalKem_bind, mem_support_bind_iff] at modeSupport
  obtain ⟨original, sourceSupport, dispatched⟩ := modeSupport
  have same := dispatch_pending env baseImpl kem attachedVerify primitives program post keys.2 original prepared ephemeral dispatched
  subst prepared
  exact prefix_history env baseImpl kem attachedVerify primitives program post c keys.2 keys.1 original sourceSupport

/-- Counting actual prior observations bounds every disclosed32-byte candidate, including duplicate values, without assuming byte distinctness. -/
theorem known_length (disclosed : List RatchetChain) (history : RawCtxProtocolReveals.History S B) :
    PqxdhInitialHistoryBudget.knownLength disclosed history ≤ disclosed.length + history.observations.length := by
  simp only [PqxdhInitialHistoryBudget.knownLength, RawCtxFamilyFreshnessProxy.knownInputs,
    RawCtxLiveLineage.known, List.length_map, List.length_append]
  apply Nat.add_le_add_left
  induction history.observations with
  | nil => simp
  | cons entry entries ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have one := RawCtxLiveLineage.disclosed_length entry.2
    omega

/-- Every source input actually prepared by the authenticated protocol supplies the full evolving-chain resource certificate, derived from original caller/callback caps and its actual initial-plus-prefix disclosure history. -/
theorem supported_caps (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64)
    (ancestors disclosed : List RatchetChain)
    (actual : PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X) (Response := Response) (A := A) (S := S) (B := B) (setup := setup))
    (supported : Sum.inr actual ∈ support (prior env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed)) :
    PqxdhInitialSampledResources.Caps actual (postCap env baseImpl kem program post c)
      (callbackCap env baseImpl kem program post c) (callbackCap env baseImpl kem program post c)
      (selectorCap env baseImpl kem program post c) c.qAux (knownCap env baseImpl kem program post c disclosed) := by
  simp only [prior, support_map] at supported
  obtain ⟨context, preparedSupport, equality⟩ := supported
  cases mode : context.state with
  | completed decision =>
    simp only [input, mode] at equality
    cases equality
  | pending prepared ephemeral =>
    have history := prepared_history env baseImpl kem attachedVerify primitives program post c context preparedSupport prepared ephemeral mode
    have caps := callbacks env baseImpl kem attachedVerify primitives program post c context.secretKey context.ciphertext
    simp only [input, mode] at equality
    cases equality
    refine ⟨?_, caps.1, caps.2.1, caps.2.2.1, caps.2.2.2, ?_⟩
    · exact post_total env baseImpl kem program post c prepared.1.context.selection.1
    · have known := known_length (S := S) (B := B + 1) disclosed prepared.1.context.selection.2.roles.2
      apply known.trans
      change disclosed.length + prepared.1.context.selection.2.roles.2.observations.length ≤ _
      unfold knownCap
      omega

/-- The actual prepared source sampler pays the original key generation, preparation, base and decapsulation work, and encapsulation before any independent root or initial expansion draw. -/
theorem prior_uniform (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64)
    (ancestors disclosed : List RatchetChain) :
    (prior env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed).IsTotalQueryBound
      (c.qKeygen + ((c.uPre + c.qBase * c.bPre + c.qDecap * c.dPre) + c.qEncap)) := by
  apply (isQueryBound_map_iff _ _ _ _ _).2
  exact PqxdhCorrelatedExtractQueryBounds.prepare_uniform_bound baseImpl kem
    (protocol env kem attachedVerify primitives program post) _ _ _ _ _ _ _ _ _ _ _
    (PqxdhAuthenticatedRootBudgets.sampler_bounds env baseImpl kem attachedVerify primitives program post c)

end BeaconcryptCore.Computational.PqxdhInitialPreparedSourceCaps

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedSourceCaps.post_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedSourceCaps.post_total

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedSourceCaps.interpreted_callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedSourceCaps.interpreted_callback

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedSourceCaps.selector_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedSourceCaps.selector_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedSourceCaps.callbacks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedSourceCaps.callbacks

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedSourceCaps.dispatch_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedSourceCaps.dispatch_pending

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedSourceCaps.prefix_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedSourceCaps.prefix_history

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedSourceCaps.prepared_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedSourceCaps.prepared_history

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedSourceCaps.known_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedSourceCaps.known_length

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedSourceCaps.supported_caps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedSourceCaps.supported_caps

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedSourceCaps.prior_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedSourceCaps.prior_uniform
