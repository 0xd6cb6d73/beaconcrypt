import BeaconcryptCore.Computational.PqxdhLivePrivateFinish
import BeaconcryptCore.Computational.PqxdhLivePhase2PrivateBounds
import BeaconcryptCore.Computational.RawCtxRevealBudgets

/-!
Seven original source classes retain every adaptive record/public/reveal/finish request. Concrete per-request callback bills compose across all optional replies without dropping repeated finish attempts or charging opaque primitive work as free ambient work. Creation, prefix and reservation costs are additional enclosing source operations.
-/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLivePrivateFinishBounds
open PqxdhLivePrivateFinish PqxdhLivePhase2PrivateRoot PqxdhKemIndCca PqxdhJointIdentity PqxdhJointKdfGame
open PqxdhPrivateKemSource PqxdhChallengeSecretRouting PqxdhChallengeSecretQueryBounds
open PqxdhLivePhase2Aux (Identity LocalSpec)
open PqxdhLiveKemRouting (PrivateKeys)
variable {ι KemSK M P D A Response : Type} {baseSpec : OracleSpec ι} {S B : Nat}

/-- Original five record/public classes, followed by actual chain reads and native finish attempts. -/
abbrev Kind := RawCtxServerServiceBounds.Kind ⊕ Bool

def kind : (PqxdhPhase2LiveFinish.Spec S B).Domain → Kind
  | .inl (.inl query) => .inl (RawCtxProtocolBudgets.sourceKind query)
  | .inl (.inr _) => .inr false
  | .inr _ => .inr true

abbrev Budget := Kind → Nat

def uniformCost (qLocal uDecap : Nat) : Kind → Nat
  | .inl original => RawCtxServerServiceBounds.uniformWeight 0 original
  | .inr false => 0
  | .inr true => 69 * max (max qLocal 64) uDecap

def finishCost (cost : Nat) : Kind → Nat
  | .inr true => cost
  | _ => 0

/-- Budgets constrain every reply continuation of the original source client. -/
def Bounded {Result : Type} (client : OracleComp (PqxdhPhase2LiveFinish.Spec S B) Result) (budget : Budget) : Prop :=
  ∀ selected, client.IsQueryBoundP (fun query => kind query = selected) (budget selected)

/-- Original live record/public/reveal execution keeps exactly its existing source uniform allowance. -/
theorem old_uniform (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Aeneas.Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (state : State M P D A S B) :
    ((old (baseSpec := baseSpec) source writer senderId route read query).run state).IsQueryBoundP
      (PublicClass (baseSpec := baseSpec) IsMlKemUniformQuery) (RawCtxRevealBudgets.weight (RawCtxServerServiceBounds.uniformWeight 0) 0 query) := by
  apply RawCtxSourceOpen.simulate_bound PqxdhBeaconPhase2Routed.publicLift IsMlKemUniformQuery
    (PublicClass (baseSpec := baseSpec) IsMlKemUniformQuery)
  · apply PqxdhPrivateRootQueryBounds.ccaCoins_uniform
    simpa only [PqxdhRegistrationProtocolState.sourceImpl, StateT.run, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
      RawCtxRevealBudgets.source_uniform_step source writer S B senderId route read query
        (PqxdhRegistrationProtocolState.project state.1)
  · exact fun request => (isQueryBoundP_query_iff (spec := LocalPostSpec baseSpec)
      (p := PublicClass (baseSpec := baseSpec) IsMlKemUniformQuery) (.inl request) _).mpr
      (by by_cases selected : IsMlKemUniformQuery request <;> simp [PublicClass, selected])

/-- Ordinary source coins cannot become base, selected decapsulation or private-root requests. This retains the complete original source program. -/
theorem old_excluded (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Aeneas.Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (state : State M P D A S B)
    (predicate : (LocalPostSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (excluded : ∀ coin, ¬ predicate (.inl (.inl (.inl coin)))) :
    ((old (baseSpec := baseSpec) source writer senderId route read query).run state).IsQueryBoundP predicate 0 := by
  apply RawCtxSourceOpen.simulate_bound PqxdhBeaconPhase2Routed.publicLift (fun request => predicate (.inl request)) predicate
  · exact PqxdhPrivateRootQueryBounds.ccaCoins_excluded _ _ excluded
  · exact fun request => (isQueryBoundP_query_iff (spec := LocalPostSpec baseSpec)
      (p := predicate) (.inl request) _).mpr
      (by by_cases selected : predicate (.inl request) <;> simp [selected])

/-- Every original record/public/chain-read request has its actual uniform bill and no KEM or private-root request. -/
theorem old_classes (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Aeneas.Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (state : State M P D A S B) :
    PostBounds ((old (baseSpec := baseSpec) source writer senderId route read query).run state)
      (RawCtxRevealBudgets.weight (RawCtxServerServiceBounds.uniformWeight 0) 0 query) 0 0 0 := by
  exact ⟨old_uniform source writer senderId route read query state,
    old_excluded source writer senderId route read query state _ (fun _ => id),
    old_excluded source writer senderId route read query state _ (fun _ => id),
    old_excluded source writer senderId route read query state _ (fun _ => id)⟩

set_option backward.isDefEq.respectTransparency false in
/-- The actual source request class charges all native finish work and each original public operation separately. Every optional branch is covered. -/
theorem service_classes (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (selected : Nat) (target : MlKem768PublicKey)
    (keys : PrivateKeys KemSK) (source : FixedHkdfSha512NoSaltSource)
    (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (senderId : M → Aeneas.Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder) (challenge : MlKem768Ciphertext)
    (qLocal uDecap bDecap : Nat)
    (localBound : ∀ query state, ((callbacks query).run state).IsTotalQueryBound qLocal)
    (uniformBound : ∀ secret ciphertext, (kem.decaps secret ciphertext).IsQueryBoundP
      (fun query => IsMlKemUniformQuery (.inl query)) uDecap)
    (baseBound : ∀ secret ciphertext, (kem.decaps secret ciphertext).IsQueryBoundP
      (fun query => IsMlKemBaseQuery (.inl query)) bDecap)
    (query : (PqxdhPhase2LiveFinish.Spec S B).Domain) (state : State M P D A S B) :
    PostBounds ((service primitives kem selected target keys source callbacks writer senderId route read challenge query).run state)
      (uniformCost qLocal uDecap (kind query)) (finishCost (69 * bDecap) (kind query))
      (finishCost 1 (kind query)) (finishCost 1 (kind query)) := by
  cases query with
  | inl query =>
    cases query <;> exact old_classes source writer senderId route read _ state
  | inr query =>
    cases query with
    | finish index raw =>
      have bounded := PqxdhLivePhase2PrivateBounds.private_owner_classes primitives kem selected keys source callbacks
        qLocal uDecap bDecap localBound uniformBound baseBound challenge read raw
        (PqxdhBeaconPhase1Publication.mapState id (encode selected) (state.1.roles.1.2 index))
        ((state.1.primitive, state.2.1), [])
      constructor <;> first
      | simpa only [service, finish, StateT.run, isQueryBoundP_map_iff, uniformCost, finishCost, kind] using bounded.uniforms
      | simpa only [service, finish, StateT.run, isQueryBoundP_map_iff, uniformCost, finishCost, kind] using bounded.bases
      | simpa only [service, finish, StateT.run, isQueryBoundP_map_iff, uniformCost, finishCost, kind] using bounded.decaps
      | simpa only [service, finish, StateT.run, isQueryBoundP_map_iff, uniformCost, finishCost, kind] using bounded.privateRoots

/-- All native finish attempts, including rejection and repetition, spend their own source coordinate. -/
theorem finish_bill (cost : Nat) (budget : Budget) :
    (∑ selected, finishCost cost selected * budget selected) = cost * budget (.inr true) := by
  simp [Fintype.sum_sum_type, finishCost]

/-- The closed uniform bill includes every original record/public coin and every repeated native callback allowance. -/
theorem uniform_bill (qLocal uDecap : Nat) (budget : Budget) :
    (∑ selected, uniformCost qLocal uDecap selected * budget selected) =
      budget (.inl .coin) + 64 * (budget (.inl .send) + budget (.inl .raw) + budget (.inl .hash)) +
        69 * max (max qLocal 64) uDecap * budget (.inr true) := by
  simp only [Fintype.sum_sum_type, uniformCost, Fintype.sum_bool, Nat.zero_mul, Nat.add_zero]
  simpa only [RawCtxServerServiceBounds.bill, Nat.zero_mul, Nat.add_zero] using
    congrArg (fun original => original + 69 * max (max qLocal 64) uDecap * budget (.inr true))
      (RawCtxServerServiceBounds.uniform_bill 0 (fun original => budget (.inl original)))

set_option backward.isDefEq.respectTransparency false in
/-- All seven source classes compose across the complete adaptive live scheduler and every optional continuation. No finish or original public work is omitted. -/
theorem schedule_classes {Result : Type} (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (selected : Nat) (target : MlKem768PublicKey)
    (keys : PrivateKeys KemSK) (source : FixedHkdfSha512NoSaltSource)
    (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (senderId : M → Aeneas.Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder) (challenge : MlKem768Ciphertext)
    (qLocal uDecap bDecap : Nat)
    (localBound : ∀ query state, ((callbacks query).run state).IsTotalQueryBound qLocal)
    (uniformBound : ∀ secret ciphertext, (kem.decaps secret ciphertext).IsQueryBoundP
      (fun query => IsMlKemUniformQuery (.inl query)) uDecap)
    (baseBound : ∀ secret ciphertext, (kem.decaps secret ciphertext).IsQueryBoundP
      (fun query => IsMlKemBaseQuery (.inl query)) bDecap)
    (client : OracleComp (PqxdhPhase2LiveFinish.Spec S B) Result) (budget : Budget)
    (bounded : Bounded client budget) (state : State M P D A S B) :
    PostBounds ((simulateQ (service primitives kem selected target keys source callbacks writer senderId route read challenge) client).run state)
      (budget (.inl .coin) + 64 * (budget (.inl .send) + budget (.inl .raw) + budget (.inl .hash)) +
        69 * max (max qLocal 64) uDecap * budget (.inr true))
      (69 * bDecap * budget (.inr true)) (budget (.inr true)) (budget (.inr true)) := by
  have steps := service_classes (P := P) (S := S) (B := B) primitives kem selected target keys source callbacks writer senderId route read challenge
    qLocal uDecap bDecap localBound uniformBound baseBound
  constructor
  · simpa only [uniform_bill] using FinitePartitionQueryBounds.weighted_bound kind (uniformCost qLocal uDecap) budget
      (service primitives kem selected target keys source callbacks writer senderId route read challenge)
      (PublicClass (baseSpec := baseSpec) IsMlKemUniformQuery) client bounded
      (fun query before => (steps query before).uniforms) state
  · simpa only [finish_bill] using FinitePartitionQueryBounds.weighted_bound kind (finishCost (69 * bDecap)) budget
      (service primitives kem selected target keys source callbacks writer senderId route read challenge)
      (PublicClass (baseSpec := baseSpec) IsMlKemBaseQuery) client bounded
      (fun query before => (steps query before).bases) state
  · simpa only [finish_bill, Nat.one_mul] using FinitePartitionQueryBounds.weighted_bound kind (finishCost 1) budget
      (service primitives kem selected target keys source callbacks writer senderId route read challenge)
      (PublicClass (baseSpec := baseSpec) IsMlKemLogicalDecapsulationQuery) client bounded
      (fun query before => (steps query before).decaps) state
  · simpa only [finish_bill, Nat.one_mul] using FinitePartitionQueryBounds.weighted_bound kind (finishCost 1) budget
      (service primitives kem selected target keys source callbacks writer senderId route read challenge)
      (IsPrivateRoot (baseSpec := baseSpec)) client bounded
      (fun query before => (steps query before).privateRoots) state

set_option backward.isDefEq.respectTransparency false in
/-- Ordinary CCA routing charges at most one selected decapsulation per complete finish, without adding a second query for the private root. -/
theorem ordinary_step (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (selected : Nat) (target : MlKem768PublicKey)
    (keys : PrivateKeys KemSK) (source : FixedHkdfSha512NoSaltSource)
    (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (senderId : M → Aeneas.Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder) (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (qLocal uDecap bDecap : Nat)
    (localBound : ∀ query state, ((callbacks query).run state).IsTotalQueryBound qLocal)
    (uniformBound : ∀ secret ciphertext, (kem.decaps secret ciphertext).IsQueryBoundP
      (fun query => IsMlKemUniformQuery (.inl query)) uDecap)
    (baseBound : ∀ secret ciphertext, (kem.decaps secret ciphertext).IsQueryBoundP
      (fun query => IsMlKemBaseQuery (.inl query)) bDecap)
    (query : (PqxdhPhase2LiveFinish.Spec S B).Domain) (state : State M P D A S B) :
    let work := simulateQ (PqxdhChallengeSecretRouting.route source challenge supplied)
      ((service primitives kem selected target keys source callbacks writer senderId route read challenge query).run state)
    work.IsQueryBoundP IsMlKemUniformQuery (uniformCost qLocal uDecap (kind query)) ∧
      work.IsQueryBoundP IsMlKemBaseQuery (finishCost (69 * bDecap) (kind query)) ∧
      work.IsQueryBoundP IsMlKemLogicalDecapsulationQuery (finishCost 1 (kind query)) := by
  cases query with
  | inl query =>
    have bounded := old_classes (baseSpec := baseSpec) source writer senderId route read query state
    have complete := And.intro
      (route_public_bound source challenge supplied IsMlKemUniformQuery (fun _ => id) _ _ bounded.uniforms)
      (And.intro
        (route_public_bound source challenge supplied IsMlKemBaseQuery (fun _ => id) _ _ bounded.bases)
        (route_decapsulation_bound source challenge supplied _ _ _ bounded.decaps bounded.privateRoots))
    cases query <;> exact complete
  | inr query =>
    cases query with
    | finish index raw =>
      simpa only [service, finish, StateT.run, simulateQ_map, isQueryBoundP_map_iff, uniformCost, finishCost, kind] using
        PqxdhLivePhase2PrivateBounds.ordinary_owner_classes primitives kem selected keys source callbacks
          qLocal uDecap bDecap localBound uniformBound baseBound challenge supplied read raw
          (PqxdhBeaconPhase1Publication.mapState id (encode selected) (state.1.roles.1.2 index))
          ((state.1.primitive, state.2.1), [])

set_option backward.isDefEq.respectTransparency false in
/-- The concrete public CCA continuation has the complete seven-class ledger and at most one selected decapsulation per actual finish, across all replies and adaptive stopping. -/
theorem ordinary_post {Result : Type} (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (selected : Nat) (target : MlKem768PublicKey)
    (keys : PrivateKeys KemSK) (source : FixedHkdfSha512NoSaltSource)
    (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (senderId : M → Aeneas.Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder) (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (qLocal uDecap bDecap : Nat)
    (localBound : ∀ query state, ((callbacks query).run state).IsTotalQueryBound qLocal)
    (uniformBound : ∀ secret ciphertext, (kem.decaps secret ciphertext).IsQueryBoundP
      (fun query => IsMlKemUniformQuery (.inl query)) uDecap)
    (baseBound : ∀ secret ciphertext, (kem.decaps secret ciphertext).IsQueryBoundP
      (fun query => IsMlKemBaseQuery (.inl query)) bDecap)
    (client : OracleComp (PqxdhPhase2LiveFinish.Spec S B) Result) (budget : Budget)
    (bounded : Bounded client budget) (state : State M P D A S B) :
    let work := simulateQ (PqxdhChallengeSecretRouting.route source challenge supplied)
      (post primitives kem selected target keys source callbacks writer senderId route read challenge client state)
    work.IsQueryBoundP IsMlKemUniformQuery
        (budget (.inl .coin) + 64 * (budget (.inl .send) + budget (.inl .raw) + budget (.inl .hash)) +
          69 * max (max qLocal 64) uDecap * budget (.inr true)) ∧
      work.IsQueryBoundP IsMlKemBaseQuery (69 * bDecap * budget (.inr true)) ∧
      work.IsQueryBoundP IsMlKemLogicalDecapsulationQuery (budget (.inr true)) := by
  simp only [post, simulateQ_map, isQueryBoundP_map_iff, QueryImpl.simulateQ_mapStateTBase_run]
  have steps := ordinary_step (P := P) (S := S) (B := B) primitives kem selected target keys source callbacks
    writer senderId route read challenge supplied qLocal uDecap bDecap localBound uniformBound baseBound
  refine ⟨?_, ?_, ?_⟩
  · simpa only [uniform_bill] using FinitePartitionQueryBounds.weighted_bound kind (uniformCost qLocal uDecap) budget
      ((PqxdhChallengeSecretRouting.route source challenge supplied).mapStateTBase
        (service primitives kem selected target keys source callbacks writer senderId route read challenge))
      IsMlKemUniformQuery client bounded (fun query before => (steps query before).1) state
  · simpa only [finish_bill] using FinitePartitionQueryBounds.weighted_bound kind (finishCost (69 * bDecap)) budget
      ((PqxdhChallengeSecretRouting.route source challenge supplied).mapStateTBase
        (service primitives kem selected target keys source callbacks writer senderId route read challenge))
      IsMlKemBaseQuery client bounded (fun query before => (steps query before).2.1) state
  · simpa only [finish_bill, Nat.one_mul] using FinitePartitionQueryBounds.weighted_bound kind (finishCost 1) budget
      ((PqxdhChallengeSecretRouting.route source challenge supplied).mapStateTBase
        (service primitives kem selected target keys source callbacks writer senderId route read challenge))
      IsMlKemLogicalDecapsulationQuery client bounded (fun query before => (steps query before).2.2) state

/-- Every original source operation remains counted, including deterministic public HKDF, compromise reads and rejected finish attempts. -/
theorem total_bound {Result : Type} (client : OracleComp (PqxdhPhase2LiveFinish.Spec S B) Result)
    (budget : Budget) (bounded : Bounded client budget) :
    client.IsTotalQueryBound (FinitePartitionQueryBounds.bill (fun _ => 1) budget) := by
  refine IsQueryBound.proj (FinitePartitionQueryBounds.bill (fun _ => 1)) ?_ ?_
    (FinitePartitionQueryBounds.structural kind client budget bounded)
  all_goals
    intro query current positive
    have exactBill := FinitePartitionQueryBounds.bill_step (fun _ => 1) current (kind query) positive
    omega

/-- The original API allowance is the sum of sends, raw receives, caller coins, public hashes, public HKDF, reads and finish attempts. -/
theorem source_queries {Result : Type} (client : OracleComp (PqxdhPhase2LiveFinish.Spec S B) Result)
    (budget : Budget) (bounded : Bounded client budget) :
    client.IsTotalQueryBound (budget (.inl .send) + budget (.inl .raw) + budget (.inl .coin) +
      budget (.inl .hash) + budget (.inl .hkdf) + budget (.inr false) + budget (.inr true)) := by
  have enumeration : (Finset.univ : Finset RawCtxServerServiceBounds.Kind) = {.send, .raw, .coin, .hash, .hkdf} := by decide
  simpa [FinitePartitionQueryBounds.bill, Fintype.sum_sum_type, enumeration, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    total_bound client budget bounded

end BeaconcryptCore.Computational.PqxdhLivePrivateFinishBounds

/-- info: 'BeaconcryptCore.Computational.PqxdhLivePrivateFinishBounds.old_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePrivateFinishBounds.old_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePrivateFinishBounds.old_excluded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePrivateFinishBounds.old_excluded
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePrivateFinishBounds.old_classes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePrivateFinishBounds.old_classes
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePrivateFinishBounds.service_classes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePrivateFinishBounds.service_classes
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePrivateFinishBounds.finish_bill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePrivateFinishBounds.finish_bill
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePrivateFinishBounds.uniform_bill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePrivateFinishBounds.uniform_bill
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePrivateFinishBounds.schedule_classes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePrivateFinishBounds.schedule_classes
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePrivateFinishBounds.ordinary_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePrivateFinishBounds.ordinary_step
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePrivateFinishBounds.ordinary_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePrivateFinishBounds.ordinary_post
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePrivateFinishBounds.total_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePrivateFinishBounds.total_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePrivateFinishBounds.source_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePrivateFinishBounds.source_queries
