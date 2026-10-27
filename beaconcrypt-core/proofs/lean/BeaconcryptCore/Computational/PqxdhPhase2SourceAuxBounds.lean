import BeaconcryptCore.Computational.PqxdhPhase2SourceAux
import BeaconcryptCore.Computational.PqxdhPhase2PreChallenge
import BeaconcryptCore.Computational.PqxdhPhase2CcaBounds

/-!
Concrete source auxiliary costs instantiate the complete native prechallenge and routed Phase2 ledgers. The same local state, reached CTX cache and entire borrowed identity history remain in every result. These syntactic bounds charge actual local callback coins and shared hash work, without a generator interchange or new cryptographic premise. The selected KEM handle and source-leaf representation must still be established by the consuming live scheduler.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPhase2SourceAuxBounds
open PqxdhPhase2SourceAux PqxdhKemIndCca PqxdhPrivateKemSource PqxdhJointKdfGame
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhGeneratedBeaconState
open PqxdhChallengeSecretRouting PqxdhPhase1AcceptanceOracle
open PqxdhPhase2JointIdentity (Converted)
open PqxdhChallengeSecretQueryBounds

variable {ι I D K X Response A : Type} {baseSpec : OracleSpec ι}

/-- Actual prechallenge source callbacks preserve the full cache/identity state and require only their concrete uniform budget; the conservative selected-decapsulation bound is explicit. -/
theorem pre_classes
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (qLocal : Nat) (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : PqxdhBeaconPhase2Preparation.State (IdentityHandle I) D (Option K))
    (auxiliary : SharedState A × BareState count) :
    let aux := borrowedAux (baseSpec := baseSpec) attachedVerify primitives count source localImpl
    let run := (simulateQ (PqxdhPhase2PreChallenge.pre source aux)
      (PqxdhBeaconPhase2Publication.nativeOwner decode raw state)).run auxiliary
    run.IsQueryBoundP IsMlKemUniformQuery (69 * max qLocal 64) ∧
      run.IsQueryBoundP IsMlKemBaseQuery 0 ∧
      run.IsQueryBoundP IsMlKemLogicalDecapsulationQuery 69 := by
  have bounds := borrowed_classes (baseSpec := baseSpec) attachedVerify primitives count source localImpl qLocal localBound
  simpa only [Nat.mul_zero, Nat.zero_add, Nat.mul_one] using
    PqxdhPhase2PreChallenge.owner_pre_classes source
      (borrowedAux attachedVerify primitives count source localImpl) (max qLocal 64) 0 0
      (fun query auxiliary => (bounds query auxiliary).1)
      (fun query auxiliary => (bounds query auxiliary).2.1)
      (fun query auxiliary => (bounds query auxiliary).2.2) decode raw state auxiliary

/-- Concrete postchallenge source auxiliary work retains one selected decapsulation and one private root, with no selected KEM secret in the executable handler. -/
theorem post_classes
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (qLocal : Nat) (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (challenge : MlKem768Ciphertext) (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : PqxdhBeaconPhase2Preparation.State (IdentityHandle I) D (Option K))
    (auxiliary : SharedState A × BareState count) :
    PostBounds ((simulateQ (PqxdhBeaconPhase2Routed.handles source challenge
      (borrowedAux (baseSpec := baseSpec) attachedVerify primitives count source localImpl))
      (PqxdhBeaconPhase2Shared.owner decode raw state)).run auxiliary)
      (69 * max qLocal 64) 0 1 1 := by
  have bounds := borrowed_classes (baseSpec := baseSpec) attachedVerify primitives count source localImpl qLocal localBound
  simpa only [Nat.mul_zero, Nat.zero_add] using
    PqxdhBeaconPhase2RoutedBounds.owner_classes source challenge
      (borrowedAux attachedVerify primitives count source localImpl) (max qLocal 64) 0 0
      (fun query auxiliary => (bounds query auxiliary).1)
      (fun query auxiliary => (bounds query auxiliary).2.1)
      (fun query auxiliary => (bounds query auxiliary).2.2) decode raw state auxiliary

/-- The ordinary interpretation charges the source callback uniforms and at most one selected decapsulation. Root evaluation adds no extra ordinary query, while its actual local computation remains present. -/
theorem ordinary_classes
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (qLocal : Nat) (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : PqxdhBeaconPhase2Preparation.State (IdentityHandle I) D (Option K))
    (auxiliary : SharedState A × BareState count) :
    let run := simulateQ (route source challenge supplied)
      ((simulateQ (PqxdhBeaconPhase2Routed.handles source challenge
        (borrowedAux (baseSpec := baseSpec) attachedVerify primitives count source localImpl))
        (PqxdhBeaconPhase2Shared.owner decode raw state)).run auxiliary)
    run.IsQueryBoundP IsMlKemUniformQuery (69 * max qLocal 64) ∧
      run.IsQueryBoundP IsMlKemBaseQuery 0 ∧
      run.IsQueryBoundP IsMlKemLogicalDecapsulationQuery 1 := by
  have bounds := borrowed_classes (baseSpec := baseSpec) attachedVerify primitives count source localImpl qLocal localBound
  simpa only [Nat.mul_zero, Nat.zero_add] using
    PqxdhPhase2CcaBounds.owner_classes source challenge supplied
      (borrowedAux attachedVerify primitives count source localImpl) (max qLocal 64) 0 0
      (fun query auxiliary => (bounds query auxiliary).1)
      (fun query auxiliary => (bounds query auxiliary).2.1)
      (fun query auxiliary => (bounds query auxiliary).2.2) decode raw state auxiliary

/-- The actual prechallenge result, complete native owner and borrowed identity/cache state enter a continuation with its explicit ordinary bill. -/
theorem pre_continuation_classes {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (qLocal : Nat) (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : PqxdhBeaconPhase2Preparation.State (IdentityHandle I) D (Option K))
    (auxiliary : SharedState A × BareState count)
    (next : ((Option Pqxdh.Bytes × PqxdhBeaconPhase2Preparation.State (IdentityHandle I) D (Option K)) ×
      (SharedState A × BareState count)) → OracleComp (MlKemCCAOracleSpec baseSpec) Result)
    (uNext bNext dNext : Nat)
    (nextBound : ∀ result, (next result).IsQueryBoundP IsMlKemUniformQuery uNext ∧
      (next result).IsQueryBoundP IsMlKemBaseQuery bNext ∧
      (next result).IsQueryBoundP IsMlKemLogicalDecapsulationQuery dNext) :
    let run := ((simulateQ (PqxdhPhase2PreChallenge.pre source
      (borrowedAux attachedVerify primitives count source localImpl))
      (PqxdhBeaconPhase2Publication.nativeOwner decode raw state)).run auxiliary) >>= next
    run.IsQueryBoundP IsMlKemUniformQuery (69 * max qLocal 64 + uNext) ∧
      run.IsQueryBoundP IsMlKemBaseQuery bNext ∧
      run.IsQueryBoundP IsMlKemLogicalDecapsulationQuery (69 + dNext) := by
  have before := pre_classes (baseSpec := baseSpec) attachedVerify primitives count source localImpl
    qLocal localBound decode raw state auxiliary
  refine ⟨isQueryBoundP_bind before.1 (fun result _ => (nextBound result).1), ?_,
    isQueryBoundP_bind before.2.2 (fun result _ => (nextBound result).2.2)⟩
  simpa only [Nat.zero_add] using isQueryBoundP_bind before.2.1 (fun result _ => (nextBound result).2.1)

/-- The same full postchallenge continuation retains independent ordinary and private-root costs, including any additional roots requested afterward. -/
theorem post_continuation_classes {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (qLocal : Nat) (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (challenge : MlKem768Ciphertext) (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : PqxdhBeaconPhase2Preparation.State (IdentityHandle I) D (Option K))
    (auxiliary : SharedState A × BareState count)
    (next : ((Option Pqxdh.Bytes × PqxdhBeaconPhase2Preparation.State (IdentityHandle I) D (Option K)) ×
      (SharedState A × BareState count)) → OracleComp (LocalPostSpec baseSpec) Result)
    (uNext bNext dNext rNext : Nat)
    (nextBound : ∀ result, PostBounds (next result) uNext bNext dNext rNext) :
    PostBounds (((simulateQ (PqxdhBeaconPhase2Routed.handles source challenge
      (borrowedAux attachedVerify primitives count source localImpl))
      (PqxdhBeaconPhase2Shared.owner decode raw state)).run auxiliary) >>= next)
      (69 * max qLocal 64 + uNext) bNext (1 + dNext) (1 + rNext) := by
  have before := post_classes (baseSpec := baseSpec) attachedVerify primitives count source localImpl
    qLocal localBound challenge decode raw state auxiliary
  refine ⟨isQueryBoundP_bind before.uniforms (fun result _ => (nextBound result).uniforms), ?_,
    isQueryBoundP_bind before.decaps (fun result _ => (nextBound result).decaps),
    isQueryBoundP_bind before.privateRoots (fun result _ => (nextBound result).privateRoots)⟩
  simpa only [Nat.zero_add] using isQueryBoundP_bind before.bases (fun result _ => (nextBound result).bases)

/-- The ordinary routed continuation is charged from its complete actual result and private state; supplied secret bytes occur only in this private interpreter. -/
theorem ordinary_continuation_classes {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (qLocal : Nat) (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : PqxdhBeaconPhase2Preparation.State (IdentityHandle I) D (Option K))
    (auxiliary : SharedState A × BareState count)
    (next : ((Option Pqxdh.Bytes × PqxdhBeaconPhase2Preparation.State (IdentityHandle I) D (Option K)) ×
      (SharedState A × BareState count)) → OracleComp (LocalPostSpec baseSpec) Result)
    (uNext bNext dNext : Nat)
    (nextBound : ∀ result,
      (simulateQ (route source challenge supplied) (next result)).IsQueryBoundP IsMlKemUniformQuery uNext ∧
      (simulateQ (route source challenge supplied) (next result)).IsQueryBoundP IsMlKemBaseQuery bNext ∧
      (simulateQ (route source challenge supplied) (next result)).IsQueryBoundP IsMlKemLogicalDecapsulationQuery dNext) :
    let run := simulateQ (route source challenge supplied)
      (((simulateQ (PqxdhBeaconPhase2Routed.handles source challenge
        (borrowedAux attachedVerify primitives count source localImpl))
        (PqxdhBeaconPhase2Shared.owner decode raw state)).run auxiliary) >>= next)
    run.IsQueryBoundP IsMlKemUniformQuery (69 * max qLocal 64 + uNext) ∧
      run.IsQueryBoundP IsMlKemBaseQuery bNext ∧
      run.IsQueryBoundP IsMlKemLogicalDecapsulationQuery (1 + dNext) := by
  have before := ordinary_classes (baseSpec := baseSpec) attachedVerify primitives count source localImpl
    qLocal localBound challenge supplied decode raw state auxiliary
  simp only [simulateQ_bind]
  refine ⟨isQueryBoundP_bind before.1 (fun result _ => (nextBound result).1), ?_,
    isQueryBoundP_bind before.2.2 (fun result _ => (nextBound result).2.2)⟩
  simpa only [Nat.zero_add] using isQueryBoundP_bind before.2.1 (fun result _ => (nextBound result).2.1)

end BeaconcryptCore.Computational.PqxdhPhase2SourceAuxBounds

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceAuxBounds.pre_classes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceAuxBounds.pre_classes

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceAuxBounds.post_classes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceAuxBounds.post_classes

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceAuxBounds.ordinary_classes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceAuxBounds.ordinary_classes

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceAuxBounds.pre_continuation_classes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceAuxBounds.pre_continuation_classes

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceAuxBounds.post_continuation_classes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceAuxBounds.post_continuation_classes

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceAuxBounds.ordinary_continuation_classes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceAuxBounds.ordinary_continuation_classes
