import BeaconcryptCore.Computational.PqxdhInitialRootEventComposition
import BeaconcryptCore.Computational.PqxdhInitialNativeBudgets

/-!
The actual instrumented accepted-root program receives a conservative transparent resource bill from each original callback and the seven-plus-sixty-seven source schedule. Each ordinary root, decapsulation and base resource is counted separately; every original local random draw remains charged. No evaluated-distribution equality is used to transfer a query cap.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialRootEventBounds
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily PqxdhCorrelatedExpandHybrid
open PqxdhInitialBeaconAmbient PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhPhase1AcceptanceOracle
open PqxdhInitializerSecrecy PqxdhPhase2SourceAux PqxdhChallengeSecretRouting
open PqxdhPhase2PostSchedulerBounds PqxdhChallengeSecretQueryBounds
variable {ι I D K X Response A Result : Type} {baseSpec : OracleSpec ι} {S B : Nat}

/-- Fixed-function execution keeps the complete original per-callback random-query bill after its private analysis table is projected. -/
theorem retained_uniform (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (query : (RawCtxPendingSelectiveFamily.Spec S B).Domain) (state : RawCtxSharedPrimitive.SharedState A) :
    ((RawCtxPendingRetainedExecution.retained source writer (productionStream source.crypto) query).run state).IsTotalQueryBound 76 := by
  have same := RawCtxPendingRetainedExecution.retained_run source writer 0
    ((RawCtxPendingSelectiveFamily.Spec S B).query query : OracleComp (RawCtxPendingSelectiveFamily.Spec S B) _)
    (state, ((fun _ => none), ⟨List.Vector.replicate 32 0, 0⟩)) (Nat.zero_le _)
  simp only [simulateQ_spec_query] at same
  have empty : RawCtxSelectedParentTable.view (productionStream source.crypto) (fun _ => none) = productionStream source.crypto := by
    funext request
    rfl
  rw [empty] at same
  rw [← same]
  apply (isQueryBound_map_iff _ _ _ _ _).2
  apply (PqxdhInitialNativeBudgets.live_uniform source writer 0 query _).mono
  rcases query with ((request | opening) | ((request | sealing) | publicQuery)) | read
  all_goals simp only [PqxdhInitialNativeBudgets.liveCost]
  all_goals try omega
  rcases publicQuery with coin | bytes | request
  all_goals simp [PqxdhInitialNativeBudgets.publicCost]

def callbackBill (qLocal qAux : Nat) : Resource → Nat
  | .uniform => max 76 (max qLocal qAux)
  | _ => 1

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (qLocal : Nat) (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Base A))
    (qAux : Nat) (auxBound : ∀ query state, ((aux query).run state).IsTotalQueryBound qAux)
    (challenge : MlKem768Ciphertext)

include localBound

/-- Every actual root-free preparation/application callback retains its original uniform/base/decapsulation class and cap. -/
theorem work_bound (resource : Resource)
    (query : (PqxdhInitialRootFreeCallbacks.ActualBaseSpec I D K X Response).Domain)
    (state : RawCtxSharedPrimitive.SharedState A × BareState count) :
    (PqxdhInitialRootFreeCallbacks.work (baseSpec := baseSpec) attachedVerify primitives count source localImpl challenge query state).IsQueryBoundP
      (predicate (baseSpec := baseSpec) resource) (perCall qLocal resource) := by
  rcases query with query | (query | reply)
  all_goals
    simp only [PqxdhInitialRootFreeCallbacks.work, PqxdhInitialRootFreeCallbacks.original, simulateQ_spec_query]
    apply (handles_step attachedVerify primitives count source localImpl qLocal localBound challenge resource _ state).mono
    split_ifs <;> omega

omit localBound in
/-- Original local sampling is confined to the uniform channel and contributes no base, decapsulation or private-root query. -/
theorem coins_bound (work : ProbComp Result) (q : Nat) (bounded : work.IsTotalQueryBound q) (resource : Resource) :
    (PqxdhPrivateAcceptedRoot.localCoins (baseSpec := baseSpec) work).IsQueryBoundP
      (predicate (baseSpec := baseSpec) resource) (if resource = .uniform then q else 0) := by
  have costs := PqxdhAuthenticatedRootBudgets.localCoins_bounds (baseSpec := baseSpec) work q bounded
  cases resource with
  | uniform => exact costs.uniforms
  | base => exact costs.bases
  | decapsulation => exact costs.decaps
  | root => exact costs.privateRoots

include auxBound in
/-- Every concrete source callback has an explicit ordinary reduction bill, including all local random sampling and every public or private decapsulation capability. -/
theorem step_bound (resource : Resource)
    (query : (PqxdhInitialRootEventCompiler.Spec (baseSpec := baseSpec) (I := I) (D := D) (K := K) (X := X) (Response := Response) (S := S) (B := B)).Domain)
    (state : RawCtxSharedPrimitive.SharedState A × BareState count) :
    ((PqxdhInitialRootEventCompiler.target source writer attachedVerify primitives count localImpl aux challenge query).run state).IsQueryBoundP
      (predicate (baseSpec := baseSpec) resource) (callbackBill qLocal qAux resource) := by
  cases query with
  | inl query =>
    apply (coins_bound _ 76 ((isQueryBound_map_iff _ _ _ _ _).2 (retained_uniform source writer query state.1)) resource).mono
    cases resource <;> simp [callbackBill]
  | inr query =>
    rcases query with query | (reply | (secrets | (query | query)))
    · apply (work_bound source attachedVerify primitives count localImpl qLocal localBound challenge resource (.inl query) state).mono
      cases resource <;> simp only [perCall, callbackBill] <;> omega
    · apply (work_bound source attachedVerify primitives count localImpl qLocal localBound challenge resource (.inr (.inr reply)) state).mono
      cases resource <;> simp only [perCall, callbackBill] <;> omega
    · simp only [PqxdhInitialRootEventCompiler.target, StateT.run, bind_pure_comp, isQueryBoundP_map_iff]
      apply (PqxdhPhase2InputBytes.rootCall_bound source challenge secrets.shared secrets.dh1 secrets.dh2 secrets.dh3 secrets.dh4
        (predicate (baseSpec := baseSpec) resource)).mono
      cases resource <;> cases secrets.shared <;> simp [callbackBill, predicate, PublicClass, IsPrivateRoot]
    · simp only [PqxdhInitialRootEventCompiler.target, StateT.run, isQueryBoundP_map_iff]
      apply publicWork_bound
      cases resource with
      | uniform =>
        apply (PqxdhPrivateRootQueryBounds.borrowed_uniform_step attachedVerify primitives count query state.2).mono
        simp only [callbackBill]
        split_ifs <;> omega
      | base =>
        apply (PqxdhPrivateRootQueryBounds.borrowed_class_step attachedVerify primitives count IsMlKemBaseQuery
          (fun _ => by simp [IsMlKemBaseQuery]) query state.2).mono
        split_ifs <;> simp [callbackBill]
      | decapsulation =>
        apply (PqxdhPrivateRootQueryBounds.borrowed_class_step attachedVerify primitives count IsMlKemLogicalDecapsulationQuery
          (fun _ => by simp [IsMlKemLogicalDecapsulationQuery]) query state.2).mono
        split_ifs <;> simp [callbackBill]
      | root => exact isQueryBoundP_false _ _
    · apply (coins_bound _ qAux ((isQueryBound_map_iff _ _ _ _ _).2 (auxBound query state.1)) resource).mono
      cases resource <;> simp [callbackBill]

section Accepted
open PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver PqxdhPrivateAcceptedRoot
open PqxdhAuthenticatedRootExperiment (Post)
variable {M P KemSK : Type} {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (program : Program baseSpec setup.Context S (B + 1))
    (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (c : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program post)
    (qPost : Nat) (postTotal : ∀ choice reply, (post choice reply).IsTotalQueryBound qPost)
include postTotal

omit localBound in
/-- The actual instrumented source client retains the full seven-call first builder and every caller-bounded adaptive post request. -/
theorem client_total (prepared : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State) (ready : Ready) :
    (PqxdhInitialRootEventAccepted.client env program post prepared ready).IsTotalQueryBound (7 + qPost * 67) := by
  exact PqxdhInitialOriginPost.sequence_total env.source _ _ _ env.senderId env.route env.decode env.index env.metadata ready
    (post prepared.1.context.selection.1) qPost (postTotal _) _

omit localBound in
/-- The actual final event adds no query to the source execution; its complete target bill comes from concrete source callbacks. -/
theorem accepted_bound (prepared : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State) (ready : Ready)
    (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64) (ancestors disclosed : List RatchetChain)
    (resource : Resource) :
    (PqxdhInitialRootEventAccepted.target env attachedVerify primitives program post prepared ready selected number ancestors disclosed).IsQueryBoundP
      (predicate (baseSpec := baseSpec) resource) ((7 + qPost * 67) * callbackBill c.qLocal c.qAux resource) := by
  simp only [PqxdhInitialRootEventAccepted.target, isQueryBoundP_map_iff]
  exact PqxdhBeaconPhase2Bounds.interpreted_total_bound _ _ _ _
    (fun query state => step_bound env.source env.recordWriter attachedVerify primitives 1 env.localImpl c.qLocal c.localBound
      env.aux c.qAux c.auxBound ready.ciphertext resource query state)
    _ (client_total env program post qPost postTotal prepared ready) _

omit localBound in
/-- Both completed and pending modes have source-derived uniform, base, decapsulation and private-root caps in the same executable root-event protocol. -/
theorem sampler_bounds (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64) (ancestors disclosed : List RatchetChain) :
    SamplerBounds baseImpl kem
      (PqxdhInitialRootEventAccepted.protocol env attachedVerify primitives program post kem selected number ancestors disclosed)
      c.qKeygen c.qEncap c.qBase c.qDecap c.uPre c.bPre c.dPre
      ((7 + qPost * 67) * callbackBill c.qLocal c.qAux .uniform)
      (7 + qPost * 67) (7 + qPost * 67) (7 + qPost * 67) := by
  refine ⟨c.keygenBound, c.encapsBound, c.baseBound, c.decapsBound, ?_, ?_⟩
  · intro key
    have original := PqxdhAuthenticatedRootBudgets.prepare_bounds env baseImpl kem attachedVerify primitives program post c key
    exact ⟨original.uniforms, original.bases, original.decaps⟩
  · intro key ciphertext mode root
    cases mode with
    | completed decision => exact ⟨by trivial, by trivial, by trivial, by trivial⟩
    | pending prepared ephemeral =>
      cases root with
      | none => exact ⟨by trivial, by trivial, by trivial, by trivial⟩
      | some value =>
        have bounded := fun resource => accepted_bound attachedVerify primitives env baseImpl kem program post c qPost postTotal prepared
          (ready env.server env.application prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.after.publicKey
            ephemeral ciphertext value) selected number ancestors disclosed resource
        exact ⟨bounded .uniform, by simpa only [callbackBill, predicate, publicPredicate, PqxdhInitialRootEventAccepted.protocol, Nat.mul_one] using bounded .base,
          by simpa only [callbackBill, predicate, publicPredicate, PqxdhInitialRootEventAccepted.protocol, Nat.mul_one] using bounded .decapsulation,
          by simpa only [callbackBill, predicate, publicPredicate, PqxdhInitialRootEventAccepted.protocol, Nat.mul_one] using bounded .root⟩

omit localBound in
/-- The full root-family reduction pays the actual key generation, original preparation, source-event callbacks and one initial root before every possible continued private request. -/
theorem reduction_bounds (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64) (ancestors disclosed : List RatchetChain) :
    let nextCalls := 7 + qPost * 67
    let p := PqxdhInitialRootEventAccepted.protocol env attachedVerify primitives program post kem selected number ancestors disclosed
    let coins := c.qKeygen + ((c.uPre + c.qBase * c.bPre + c.qDecap * c.dPre) + c.qEncap) +
      (nextCalls * callbackBill c.qLocal c.qAux .uniform + c.qBase * nextCalls + c.qDecap * (nextCalls + nextCalls))
    (rootReduction env.source baseImpl kem p).IsQueryBoundP PqxdhCorrelatedExpandQueryBounds.IsCoin coins ∧
    (rootReduction env.source baseImpl kem p).IsQueryBoundP IsRoot (1 + nextCalls) := by
  exact PqxdhCorrelatedExpandQueryBounds.reduction_bounds env.source baseImpl kem
    (PqxdhInitialRootEventAccepted.protocol env attachedVerify primitives program post kem selected number ancestors disclosed)
    _ _ _ _ _ _ _ _ _ _ _ (sampler_bounds attachedVerify primitives env baseImpl kem program post c qPost postTotal selected number ancestors disclosed)

end Accepted

end BeaconcryptCore.Computational.PqxdhInitialRootEventBounds

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventBounds.retained_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventBounds.retained_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventBounds.work_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventBounds.work_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventBounds.coins_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventBounds.coins_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventBounds.step_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventBounds.step_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventBounds.client_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventBounds.client_total

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventBounds.accepted_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventBounds.accepted_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventBounds.sampler_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventBounds.sampler_bounds

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventBounds.reduction_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventBounds.reduction_bounds
