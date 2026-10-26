import BeaconcryptCore.Computational.PqxdhInitialBuilderSecrecy

/-!
The factored initializer builder pays its actual original callback classes even for an arbitrary supplied initializer result. Allocation and binding checks retain their source order; failed or divergent initializer results add no later callback. The source and randomized initializer continuations therefore use the same nine-class native ledger, rather than an opaque assumed builder budget.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialBuilderQueryBounds
open PqxdhServerRegistrationPublication PqxdhAcceptedRegistration PqxdhInitialBuilderCut

/-- Each actual candidate callback class has cap one for every initializer result, including diagnostic failure and divergence. -/
theorem candidate_bound {Metadata PeerMetadata Consumed : Type}
    (initial : RustM ConcreteRatchetKernel) (pending : pqxdh.ServerRegistrationCandidate)
    (data : Option Bytes) (metadata : PeerMetadata)
    (state : State Metadata PeerMetadata Consumed) (kind : CallKind) :
    (candidate initial pending data metadata state).IsQueryBoundP (fun query => callKind query = kind) 1 := by
  obtain ⟨binding, hbinding, _⟩ := candidate_binding pending
  simp only [candidate, hbinding, continueRust]
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inr (by decide), fun valid => ?_⟩
  cases valid
  · exact isQueryBoundP_pure _ _ _
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨by cases kind <;> simp [callKind, auxKind], fun reserved => ?_⟩
    cases reserved
    all_goals try exact isQueryBoundP_pure _ _ _
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    cases initial
    all_goals try exact isQueryBoundP_pure _ _ _
    dsimp only
    split
    all_goals try exact isQueryBoundP_pure _ _ _
    split
    all_goals try exact isQueryBoundP_pure _ _ _
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨by cases kind <;> simp [callKind, auxKind], fun allocated => ?_⟩
    cases allocated
    all_goals try exact isQueryBoundP_pure _ _ _
    simp only [Bool.not_true, Bool.false_eq_true, ite_false, isQueryBoundP_map_iff]
    apply (afterInitialization_bound pending _ _ metadata state kind).mono
    cases kind <;> simp [callKind, auxKind, afterAllowance]

/-- Pure diagnostic control adds no callback before the exact original continuation. -/
theorem continue_bound {α β ι : Type} {spec : OracleSpec ι}
    (result : RustM α) (next : α → OracleComp spec (RustM β))
    (predicate : spec.Domain → Prop) [DecidablePred predicate] (budget : Nat)
    (bounded : ∀ value, (next value).IsQueryBoundP predicate budget) :
    (continueRust result next).IsQueryBoundP predicate budget := by
  cases result
  all_goals first | exact bounded _ | exact isQueryBoundP_pure _ _ _

/-- Original binding preparation adds no callback before the bounded candidate tail, for every supplied initializer result. -/
theorem used_bound {Metadata PeerMetadata Consumed : Type}
    (initial : RustM ConcreteRatchetKernel) (pending : PqxdhRegistrationInputs.UsedInput)
    (data : Option Bytes) (metadata : PeerMetadata)
    (state : State Metadata PeerMetadata Consumed) (kind : CallKind) :
    (usedBuild initial pending data metadata state).IsQueryBoundP (fun query => callKind query = kind) 1 := by
  apply continue_bound
  rintro (_ | next)
  all_goals try exact isQueryBoundP_pure _ _ _
  apply continue_bound
  rintro (prepared | _)
  all_goals first | exact candidate_bound initial _ data metadata state kind | exact isQueryBoundP_pure _ _ _

/-- All factored accepted-root callbacks retain their source one-call cap independently of the initializer answer. -/
theorem ready_bound {Metadata PeerMetadata Consumed : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (initial : RustM ConcreteRatchetKernel)
    (binding : pqxdh.ServerBinding) (ready : PqxdhPrivateAcceptedRoot.Ready) (metadata : PeerMetadata)
    (state : State Metadata PeerMetadata Consumed) (kind : CallKind) :
    (readyBuild source initial binding ready metadata state).IsQueryBoundP
      (fun query => callKind query = kind) 1 :=
  used_bound initial _ ready.application metadata state kind

/-- The native partition names exactly the original callback predicates. -/
theorem native_class (kind : NativeKind) (query : NativeSpec.Domain) :
    nativeKind query = kind ↔ nativePredicate kind query := by
  rcases query with ((request | (request | (request | request))) | request)
  all_goals cases kind <;> try cases request
  all_goals simp [nativeKind, nativePredicate, leftPredicate, auxPredicate, auxKind,
    RawCtxSourceSeal.category, RawCtxSourceSeal.sealingPredicate, RawCtxSourceSeal.callKind]

/-- The factored builder has one-call caps on all nine original native interfaces for every initializer answer. -/
theorem native_partition {Metadata PeerMetadata Consumed : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (initial : RustM ConcreteRatchetKernel)
    (binding : pqxdh.ServerBinding) (ready : PqxdhPrivateAcceptedRoot.Ready) (metadata : PeerMetadata)
    (state : State Metadata PeerMetadata Consumed) (kind : NativeKind) :
    (simulateQ nativeAdapter (readyBuild source initial binding ready metadata state)).IsQueryBoundP
      (fun query => nativeKind query = kind) 1 := by
  apply (isQueryBoundP_congr_pred (p' := nativePredicate kind) (native_class kind)).mpr
  cases kind
  all_goals first
    | exact native_kdf_bound _ 1 (ready_bound source initial binding ready metadata state .kdf)
    | exact native_seal_bound _ 1 (ready_bound source initial binding ready metadata state .seal) .aead
    | exact native_seal_bound _ 1 (ready_bound source initial binding ready metadata state .seal) .hash
    | exact native_seal_bound _ 1 (ready_bound source initial binding ready metadata state .seal) .writer
    | exact native_aux_bound _ 1 .identity (ready_bound source initial binding ready metadata state .identity)
    | exact native_aux_bound _ 1 .peerReserve (ready_bound source initial binding ready metadata state .peerReserve)
    | exact native_aux_bound _ 1 .plaintextReserve (ready_bound source initial binding ready metadata state .plaintextReserve)
    | exact native_aux_bound _ 1 .erase (ready_bound source initial binding ready metadata state .erase)
    | exact native_aux_bound _ 1 .writer (ready_bound source initial binding ready metadata state .writer)

/-- Each interpreted callback pays its stated primitive cost; the arbitrary initializer result does not conceal any native work. -/
theorem weighted_bound {Metadata PeerMetadata Consumed PrimitiveState ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp base)))
    (predicate : base.Domain → Prop) [DecidablePred predicate] (cost : NativeKind → Nat)
    (step : ∀ query primitive, ((impl query).run primitive).IsQueryBoundP predicate (cost (nativeKind query)))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (initial : RustM ConcreteRatchetKernel)
    (binding : pqxdh.ServerBinding) (ready : PqxdhPrivateAcceptedRoot.Ready) (metadata : PeerMetadata)
    (state : State Metadata PeerMetadata Consumed) (primitive : PrimitiveState) :
    ((simulateQ impl (simulateQ nativeAdapter
      (readyBuild source initial binding ready metadata state))).run primitive).IsQueryBoundP predicate (∑ kind, cost kind) := by
  simpa only [Nat.mul_one] using FinitePartitionQueryBounds.weighted_bound nativeKind cost (fun _ => 1)
    impl predicate _ (native_partition source initial binding ready metadata state) step primitive

open PqxdhProtocolQueryBounds

/-- The exact factored protocol builder pays at most one commitment miss and five explicitly costed auxiliary calls for every initializer answer. -/
theorem protocol_uniform {M P I D K A : Type} {S B : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (initial : RustM ConcreteRatchetKernel)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (qAux : Nat) (auxBound : ∀ query primitive, ((aux query).run primitive).IsTotalQueryBound qAux)
    (senderId : M → Std.U64) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (state : PqxdhRegistrationProtocolState.State M P I D K A S B) :
    ((protocolBuild source writer initial aux senderId index metadata ready).run state).IsTotalQueryBound
      (64 + 5 * qAux) := by
  simp only [protocolBuild, StateT.run, IsTotalQueryBound, isQueryBound_map_iff]
  have bound := weighted_bound (PqxdhRegistrationProtocolState.registrationImpl source writer aux)
    (fun _ => True) (nativeUniformCost qAux)
    (fun query primitive => (native_uniform_step source writer aux qAux auxBound query primitive).isQueryBoundP)
    source initial (PqxdhRegistrationProtocolState.input senderId index metadata
      (PqxdhRegistrationProtocolState.consume index ready state)).binding ready metadata
    (PqxdhRegistrationProtocolState.input senderId index metadata
      (PqxdhRegistrationProtocolState.consume index ready state)).state state.primitive
  simpa only [native_uniform_bill, IsTotalQueryBound, IsQueryBoundP, not_true_eq_false, false_or, ite_true,
    StateT.run, PqxdhRegistrationProtocolState.consume] using bound

variable {M P I D K A Context : Type} {S B : Nat}

/-- The actual initializer observer pays the derived full builder bill before its explicitly bounded outside continuation. -/
theorem observer_uniform
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (senderId : M → Std.U64) (index : Fin S) (metadata : P)
    (ready : Context → PqxdhPrivateAcceptedRoot.Ready)
    (state : Context → PqxdhInitialBuilderSecrecy.State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B))
    (outside : Context → PqxdhInitialBuilderSecrecy.Result (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) → ProbComp Bool)
    (qAux qOutside : Nat)
    (auxBound : ∀ query primitive, ((aux query).run primitive).IsTotalQueryBound qAux)
    (outsideBound : ∀ context result, (outside context result).IsTotalQueryBound qOutside)
    (context : Context) (initial : RawCtxInitialSecrecy.Pair) :
    (PqxdhInitialBuilderSecrecy.observer source writer aux senderId index metadata ready state outside context initial).IsTotalQueryBound
      ((64 + 5 * qAux) + qOutside) := by
  exact isTotalQueryBound_bind (protocol_uniform source writer initial.1 aux qAux auxBound senderId index metadata
    (eraseRoot (ready context)) (state context)) (fun result => outsideBound context result)

open PqxdhSecretInputKdf PqxdhFullSecretInputKdf

/-- The concrete initializer reduction makes at most two HMAC challenge calls and pays the full root sampler, first-send builder and outside continuation. -/
theorem reduction_queries
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (senderId : M → Std.U64) (index : Fin S) (metadata : P)
    (sample : RawCtxInitialSecrecy.Sampler Context) (ready : Context → PqxdhPrivateAcceptedRoot.Ready)
    (state : Context → PqxdhInitialBuilderSecrecy.State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B))
    (outside : Context → PqxdhInitialBuilderSecrecy.Result (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) → ProbComp Bool)
    (qSample qAux qOutside : Nat) (sampleBound : sample.IsTotalQueryBound qSample)
    (auxBound : ∀ query primitive, ((aux query).run primitive).IsTotalQueryBound qAux)
    (outsideBound : ∀ context result, (outside context result).IsTotalQueryBound qOutside) :
    let observe := PqxdhInitialBuilderSecrecy.observer source writer aux senderId index metadata ready state outside
    (fullExpandReduction .ratchet (RawCtxInitialSecrecy.joint sample) (RawCtxInitialSecrecy.observer observe)).IsQueryBoundP
        IsHmacChallengeQuery 2 ∧
      (fullExpandReduction .ratchet (RawCtxInitialSecrecy.joint sample) (RawCtxInitialSecrecy.observer observe)).IsQueryBoundP
        PqxdhFullSecretInputKdf.IsHmacUniformQuery (qSample + ((64 + 5 * qAux) + qOutside)) := by
  exact RawCtxInitialSecrecy.reduction_bounds sample _ qSample _ sampleBound
    (observer_uniform source writer aux senderId index metadata ready state outside qAux qOutside auxBound outsideBound)

set_option maxRecDepth 2048 in
/-- Each challenger world pays its own random bytes plus the same concrete first-send and outside bill; the comparison full 76-byte draw is not assigned to the source initializer. -/
theorem challenger_queries
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (senderId : M → Std.U64) (index : Fin S) (metadata : P)
    (sample : RawCtxInitialSecrecy.Sampler Context) (ready : Context → PqxdhPrivateAcceptedRoot.Ready)
    (state : Context → PqxdhInitialBuilderSecrecy.State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B))
    (outside : Context → PqxdhInitialBuilderSecrecy.Result (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) → ProbComp Bool)
    (qSample qAux qOutside : Nat) (sampleBound : sample.IsTotalQueryBound qSample)
    (auxBound : ∀ query primitive, ((aux query).run primitive).IsTotalQueryBound qAux)
    (outsideBound : ∀ context result, (outside context result).IsTotalQueryBound qOutside) :
    let observe := RawCtxInitialSecrecy.observer
      (PqxdhInitialBuilderSecrecy.observer source writer aux senderId index metadata ready state outside)
    let joint := RawCtxInitialSecrecy.joint sample
    let qObserve := (64 + 5 * qAux) + qOutside
    (extractRealGame hmac joint (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound (qSample + qObserve) ∧
      (extractUniformGame joint (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound (qSample + (64 + qObserve)) ∧
      (hmacPrfRealGame hmac (fullExpandReduction .ratchet joint observe)).IsTotalQueryBound (64 + (qSample + qObserve)) ∧
      (hmacPrfRandomGame (fullExpandReduction .ratchet joint observe)).IsTotalQueryBound (qSample + (64 + (64 + qObserve))) ∧
      (independentFullGame joint observe).IsTotalQueryBound (qSample + (76 + qObserve)) := by
  exact RawCtxInitialSecrecy.challenger_uniform hmac sample _ qSample _ sampleBound
    (observer_uniform source writer aux senderId index metadata ready state outside qAux qOutside auxBound outsideBound)

set_option maxRecDepth 2048 in
/-- The actual randomized initializer pays exactly its 64-byte draw plus the derived original builder and explicit outside sampling budgets. -/
theorem random_queries
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (senderId : M → Std.U64) (index : Fin S) (metadata : P)
    (sample : RawCtxInitialSecrecy.Sampler Context) (ready : Context → PqxdhPrivateAcceptedRoot.Ready)
    (state : Context → PqxdhInitialBuilderSecrecy.State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B))
    (outside : Context → PqxdhInitialBuilderSecrecy.Result (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) → ProbComp Bool)
    (qSample qAux qOutside : Nat) (sampleBound : sample.IsTotalQueryBound qSample)
    (auxBound : ∀ query primitive, ((aux query).run primitive).IsTotalQueryBound qAux)
    (outsideBound : ∀ context result, (outside context result).IsTotalQueryBound qOutside) :
    (RawCtxInitialSecrecy.random sample
      (PqxdhInitialBuilderSecrecy.observer source writer aux senderId index metadata ready state outside)).IsTotalQueryBound
      (qSample + (64 + ((64 + 5 * qAux) + qOutside))) := by
  exact RawCtxInitialSecrecy.random_uniform sample _ qSample _ sampleBound
    (observer_uniform source writer aux senderId index metadata ready state outside qAux qOutside auxBound outsideBound)

end BeaconcryptCore.Computational.PqxdhInitialBuilderQueryBounds
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderQueryBounds.candidate_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderQueryBounds.candidate_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderQueryBounds.continue_bound' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderQueryBounds.continue_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderQueryBounds.used_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderQueryBounds.used_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderQueryBounds.ready_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderQueryBounds.ready_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderQueryBounds.native_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderQueryBounds.native_class

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderQueryBounds.native_partition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderQueryBounds.native_partition

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderQueryBounds.weighted_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderQueryBounds.weighted_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderQueryBounds.protocol_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderQueryBounds.protocol_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderQueryBounds.observer_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderQueryBounds.observer_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderQueryBounds.reduction_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderQueryBounds.reduction_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderQueryBounds.challenger_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderQueryBounds.challenger_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderQueryBounds.random_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderQueryBounds.random_queries
