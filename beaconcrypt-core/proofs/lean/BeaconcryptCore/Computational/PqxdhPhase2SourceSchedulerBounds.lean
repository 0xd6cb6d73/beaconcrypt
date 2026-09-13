import BeaconcryptCore.Computational.PqxdhPhase2SourceScheduler
import BeaconcryptCore.Computational.PqxdhPhase2SelectorBounds
import BeaconcryptCore.Computational.PqxdhProtocolQueryBounds

/-!
Concrete source scheduler costs retain the original record/public/reveal operations, every forwarded identity/source/CCA request and every native finish attempt. Signing and identity creation are excluded from the native compiler by its actual callback syntax. These bounds precede the later identity/base/CCA interpretation; local functional work and that interpretation's costs remain separate. No reached generation, successful finish or cryptographic premise is introduced.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPhase2SourceSchedulerBounds
open PqxdhPhase2SourceScheduler PqxdhPhase2SourceAux PqxdhPrivateKemSource PqxdhJointKdfGame
open PqxdhGeneratedBeaconState (IdentityHandle KemHandle)
open PqxdhPhase2JointIdentity (Converted)
variable {ι M P I D K X Response A : Type} {baseSpec : OracleSpec ι} {S B : Nat}

/-- The original record kinds remain separate; the six additional coordinates are reveal, source, uniform, base, decapsulation and finish. -/
abbrev Kind := RawCtxServerServiceBounds.Kind ⊕ Fin 6
abbrev Budget := Kind → Nat

def classify : (Spec baseSpec S B).Domain → Kind
  | .inl (.inl (.inl request)) => .inl (RawCtxProtocolBudgets.sourceKind request)
  | .inl (.inl (.inr _)) => .inr 0
  | .inl (.inr (.inl _)) => .inr 1
  | .inl (.inr (.inr (.inl (.inl _)))) => .inr 2
  | .inl (.inr (.inr (.inl (.inr _)))) => .inr 3
  | .inl (.inr (.inr (.inr _))) => .inr 4
  | .inr _ => .inr 5

def cost (qLocal : Nat) : Kind → Nat
  | .inl kind => RawCtxServerServiceBounds.uniformWeight 0 kind
  | .inr index => if index = 0 then 0 else if index = 5 then 69 * (max qLocal 64 + 1) else 1

def bill (qLocal : Nat) (budget : Budget) : Nat :=
  ∑ kind, cost qLocal kind * budget kind

def Bounded {Result : Type} (client : OracleComp (Spec baseSpec S B) Result) (budget : Budget) : Prop :=
  ∀ kind, client.IsQueryBoundP (fun query => classify (baseSpec := baseSpec) query = kind) (budget kind)

set_option backward.isDefEq.respectTransparency false in
/-- Mapping the private KEM handle retains one actual source callback and its complete reply state. -/
theorem native_step_total
    (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (qLocal : Nat) (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (query : (NativeSpec I D K X Response).Domain) (state : SharedState A) :
    ((sourceNative (baseSpec := baseSpec) source localImpl query).run state).IsTotalQueryBound (max qLocal 64 + 1) := by
  rcases query with (query | query)
  · cases query <;>
      simp only [sourceNative, QueryImpl.compose, PqxdhPhase2KemHandles.native,
        PqxdhPhase2KemHandles.preparation, simulateQ_spec_query]
    all_goals exact PqxdhPhase2SelectorBounds.step_total source localImpl qLocal localBound _ state
  · simp only [sourceNative, QueryImpl.compose, PqxdhPhase2KemHandles.native, simulateQ_spec_query]
    exact PqxdhPhase2SelectorBounds.step_total source localImpl qLocal localBound _ state

/-- The full native program cannot sign or create an identity, even through arbitrary optional continuations. -/
theorem native_restrictions {Result : Type}
    (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (client : OracleComp (NativeSpec I D K X Response) Result) (state : SharedState A) :
    let work := (simulateQ (sourceNative (baseSpec := baseSpec) source localImpl) client).run state
    work.IsQueryBoundP (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec)
      PqxdhJointPhase1AcceptanceComposition.IsSigning) 0 ∧
    work.IsQueryBoundP (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec)
      PqxdhPrivatePhase1Prefix.Creating) 0 := by
  simpa only [sourceNative, QueryImpl.simulateQ_compose] using
    PqxdhPhase2SelectorBounds.source_restrictions source localImpl
      (simulateQ (PqxdhPhase2KemHandles.native PqxdhPhase2KemProvenance.encode) client) state

set_option backward.isDefEq.respectTransparency false in
/-- Every actual caller class receives its concrete source cost before identity or CCA interpretation. -/
theorem compiler_step_total
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (qLocal : Nat) (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (query : (Spec baseSpec S B).Domain) (state : State M P I D K A S B) :
    ((compiler source writer senderId route decode localImpl query).run state).IsTotalQueryBound
      (cost qLocal (classify (baseSpec := baseSpec) query)) := by
  rcases query with (query | query)
  · have old := PqxdhProtocolQueryBounds.compiler_step (baseSpec := baseSpec) source writer senderId route decode query state
    rcases query with ((request | reveal) | (request | ((uniform | base) | decapsulation))) <;>
      simpa [compiler, classify, cost, PqxdhProtocolQueryBounds.compilerCost,
        RawCtxRevealBudgets.weight] using old
  · exact (isQueryBoundP_true_iff _ _).1
      (PqxdhPhase2LiveFinish.finish_query_bound (sourceNative source localImpl) decode (fun _ => True)
        (max qLocal 64 + 1) (fun request primitive => (isQueryBoundP_true_iff _ _).2
          (native_step_total source localImpl qLocal localBound request primitive)) query state)

/-- Every adaptive reply branch pays the concrete weighted bill while retaining the full result and scheduler state. -/
theorem compiler_total {Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (qLocal : Nat) (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (client : OracleComp (Spec baseSpec S B) Result) (budget : Budget) (bounded : Bounded client budget)
    (state : State M P I D K A S B) :
    ((simulateQ (compiler source writer senderId route decode localImpl) client).run state).IsTotalQueryBound
      (bill qLocal budget) := by
  exact (isQueryBoundP_true_iff _ _).1
    (FinitePartitionQueryBounds.weighted_bound (classify (baseSpec := baseSpec)) (cost qLocal) budget
      (compiler source writer senderId route decode localImpl) (fun _ => True) client bounded
      (fun query state => (isQueryBoundP_true_iff _ _).2
        (compiler_step_total source writer senderId route decode localImpl qLocal localBound query state)) state)

/-- The scalar bill retains all four forwarded-service counts and the separate finish count, including inactive attempts. -/
theorem bill_eq (qLocal : Nat) (budget : Budget) :
    bill qLocal budget = budget (.inl .coin) +
      64 * (budget (.inl .send) + budget (.inl .raw) + budget (.inl .hash)) +
      budget (.inr 1) + budget (.inr 2) + budget (.inr 3) + budget (.inr 4) +
      69 * (max qLocal 64 + 1) * budget (.inr 5) := by
  simp only [bill, Fintype.sum_sum_type]
  have old := RawCtxServerServiceBounds.uniform_bill 0 (fun kind => budget (.inl kind))
  simp only [RawCtxServerServiceBounds.bill, Nat.zero_mul, Nat.add_zero] at old
  change (∑ kind, RawCtxServerServiceBounds.uniformWeight 0 kind * budget (.inl kind)) +
    (∑ kind : Fin 6, cost qLocal (.inr kind) * budget (.inr kind)) = _
  rw [old]
  simp [Fin.sum_univ_succ, cost, Nat.add_assoc]

/-- Only the original forwarded source request is counted by this caller-side predicate. -/
def ForwardedSource (predicate : PqxdhPhase1AcceptanceOracle.SourceSpec.Domain → Prop) :
    (Spec baseSpec S B).Domain → Prop
  | .inl query => PqxdhProtocolSelector.SelectorClass
      (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) predicate) query
  | .inr _ => False

instance (predicate : PqxdhPhase1AcceptanceOracle.SourceSpec.Domain → Prop) [DecidablePred predicate] :
    DecidablePred (ForwardedSource (baseSpec := baseSpec) (S := S) (B := B) predicate)
  | .inl query => inferInstanceAs (Decidable (PqxdhProtocolSelector.SelectorClass
      (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) predicate) query))
  | .inr _ => isFalse id

set_option backward.isDefEq.respectTransparency false in
private theorem compiler_source_bound {Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (predicate : PqxdhPhase1AcceptanceOracle.SourceSpec.Domain → Prop) [DecidablePred predicate]
    (nativeZero : ∀ query primitive, ((sourceNative (baseSpec := baseSpec) source localImpl query).run primitive).IsQueryBoundP
      (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) predicate) 0)
    (client : OracleComp (Spec baseSpec S B) Result) (budget : Nat)
    (bounded : client.IsQueryBoundP (ForwardedSource (baseSpec := baseSpec) predicate) budget)
    (state : State M P I D K A S B) :
    ((simulateQ (compiler source writer senderId route decode localImpl) client).run state).IsQueryBoundP
      (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) predicate) budget := by
  apply bounded.simulateQ_run_StateT_of_step _ state
  intro query before
  cases query with
  | inl query =>
    have step := PqxdhProtocolSelector.compiler_bound source writer senderId route decode
      (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) predicate)
      (by intro coin; simp [PqxdhPrivateKemQueryBounds.SelectorSource])
      (liftM ((PqxdhProtocolSelector.Spec baseSpec S B).query query))
      (if PqxdhProtocolSelector.SelectorClass
        (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) predicate) query then 1 else 0)
      (by
        rw [isQueryBoundP_query_iff]
        intro present
        simp [present]) before
    simpa only [simulateQ_spec_query, compiler, ForwardedSource] using step
  | inr query =>
    simpa only [compiler, ForwardedSource, if_false, Nat.mul_zero] using
      PqxdhPhase2LiveFinish.finish_query_bound (sourceNative source localImpl) decode
        (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) predicate) 0 nativeZero query before

/-- Only caller-forwarded signing or creation requests contribute to those source classes; actual finish work adds neither. -/
theorem compiler_source_caps {Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (client : OracleComp (Spec baseSpec S B) Result) (qSign qCreate : Nat)
    (signBound : client.IsQueryBoundP (ForwardedSource (baseSpec := baseSpec)
      PqxdhJointPhase1AcceptanceComposition.IsSigning) qSign)
    (createBound : client.IsQueryBoundP (ForwardedSource (baseSpec := baseSpec)
      PqxdhPrivatePhase1Prefix.Creating) qCreate)
    (state : State M P I D K A S B) :
    let work := (simulateQ (compiler source writer senderId route decode localImpl) client).run state
    work.IsQueryBoundP (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec)
      PqxdhJointPhase1AcceptanceComposition.IsSigning) qSign ∧
    work.IsQueryBoundP (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec)
      PqxdhPrivatePhase1Prefix.Creating) qCreate := by
  constructor
  · exact compiler_source_bound source writer senderId route decode localImpl _
      (fun query primitive => by
        simpa only [simulateQ_spec_query] using
          (native_restrictions (baseSpec := baseSpec) source localImpl
            (liftM ((NativeSpec I D K X Response).query query)) primitive).1)
      client qSign signBound state
  · exact compiler_source_bound source writer senderId route decode localImpl _
      (fun query primitive => by
        simpa only [simulateQ_spec_query] using
          (native_restrictions (baseSpec := baseSpec) source localImpl
            (liftM ((NativeSpec I D K X Response).query query)) primitive).2)
      client qCreate createBound state

/-- A source-restricted caller remains source-restricted after the entire concrete native scheduler is compiled. -/
theorem compiler_restrictions {Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (client : OracleComp (Spec baseSpec S B) Result)
    (noSign : client.IsQueryBoundP (ForwardedSource (baseSpec := baseSpec)
      PqxdhJointPhase1AcceptanceComposition.IsSigning) 0)
    (noCreate : client.IsQueryBoundP (ForwardedSource (baseSpec := baseSpec)
      PqxdhPrivatePhase1Prefix.Creating) 0)
    (state : State M P I D K A S B) :
    let work := (simulateQ (compiler source writer senderId route decode localImpl) client).run state
    work.IsQueryBoundP (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec)
      PqxdhJointPhase1AcceptanceComposition.IsSigning) 0 ∧
    work.IsQueryBoundP (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec)
      PqxdhPrivatePhase1Prefix.Creating) 0 :=
  compiler_source_caps source writer senderId route decode localImpl client 0 0 noSign noCreate state

/-- The subsequent source continuation is charged on every complete optional result and live state, including failed finish attempts. -/
theorem compiler_continuation_total {Result Output : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (qLocal : Nat) (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (client : OracleComp (Spec baseSpec S B) Result) (budget : Budget) (bounded : Bounded client budget)
    (state : State M P I D K A S B)
    (next : Result × State M P I D K A S B → OracleComp (SelectorSpec baseSpec) Output)
    (qNext : Nat) (nextBound : ∀ result, (next result).IsTotalQueryBound qNext) :
    (((simulateQ (compiler source writer senderId route decode localImpl) client).run state) >>= next).IsTotalQueryBound
      (bill qLocal budget + qNext) := by
  exact isTotalQueryBound_bind
    (compiler_total source writer senderId route decode localImpl qLocal localBound client budget bounded state)
    nextBound

end BeaconcryptCore.Computational.PqxdhPhase2SourceSchedulerBounds

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceSchedulerBounds.native_step_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceSchedulerBounds.native_step_total
/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceSchedulerBounds.native_restrictions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceSchedulerBounds.native_restrictions
/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceSchedulerBounds.compiler_step_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceSchedulerBounds.compiler_step_total
/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceSchedulerBounds.compiler_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceSchedulerBounds.compiler_total
/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceSchedulerBounds.bill_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceSchedulerBounds.bill_eq
/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceSchedulerBounds.compiler_source_caps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceSchedulerBounds.compiler_source_caps
/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceSchedulerBounds.compiler_restrictions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceSchedulerBounds.compiler_restrictions
/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceSchedulerBounds.compiler_continuation_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceSchedulerBounds.compiler_continuation_total
