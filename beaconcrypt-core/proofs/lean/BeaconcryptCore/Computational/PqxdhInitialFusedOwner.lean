import BeaconcryptCore.Computational.PqxdhInitialFusedBeacon

/-!
The complete current Beacon owner is factored through the response-only private root/initializer service. Its original preparation, optional failures, sequence-one/binding checks, publication and complete prior state remain unchanged. No raw root reply appears in the executable tail interface. Native interpretation supplies the original private root and initializer effects in order.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialFusedOwner
variable {I D K X Response Shared Result : Type}

abbrev Spec (I D K X Response Shared : Type) :=
  PqxdhBeaconPhase2Shared.Spec I D K X Response Shared + PqxdhInitialFusedBeacon.Spec Response Shared

def preLift : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (OracleComp (Spec I D K X Response Shared)) :=
  fun query => (Spec I D K X Response Shared).query (.inl query)
def tailLift : QueryImpl (PqxdhInitialFusedBeacon.Spec Response Shared) (OracleComp (Spec I D K X Response Shared)) :=
  fun query => (Spec I D K X Response Shared).query (.inr query)

noncomputable def native : QueryImpl (Spec I D K X Response Shared)
    (OracleComp (PqxdhBeaconPhase2Shared.FullSpec I D K X Response Shared))
  | .inl query => (PqxdhBeaconPhase2Shared.FullSpec I D K X Response Shared).query (.inl query)
  | .inr query => simulateQ PqxdhBeaconPhase2Shared.tailLift (PqxdhInitialFusedBeacon.native query)

noncomputable def owner (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : PqxdhBeaconPhase2Preparation.State I D K) :
    OracleComp (Spec I D K X Response Shared) (Option Pqxdh.Bytes × PqxdhBeaconPhase2Preparation.State I D K) :=
  match state.beacon.phase with
  | .initSent control prekey oneTime kem => do
      let prepared ← simulateQ preLift (PqxdhBeaconPhase2Shared.prepare control state.beacon.identity prekey oneTime kem raw)
      match prepared with
      | none => pure (PqxdhBeaconPhase2Publication.finish control state none)
      | some prepared => do
          let staged ← simulateQ tailLift (PqxdhInitialFusedBeacon.tail decode prepared)
          pure (PqxdhBeaconPhase2Publication.finish control state staged)
  | _ => pure (none, state)

/-- Complete original preparation callbacks retain their exact order and replies before the private fused service is requested. -/
theorem pre_program (work : OracleComp (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) Result) :
    simulateQ native (simulateQ preLift work) = simulateQ PqxdhBeaconPhase2Shared.preLift work := by
  have bridge : native ∘ₛ (preLift (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared)) =
      PqxdhBeaconPhase2Shared.preLift := by
    funext query
    simp [QueryImpl.compose, preLift, native, PqxdhBeaconPhase2Shared.preLift, OracleSpec.query]
  rw [← QueryImpl.simulateQ_compose, bridge]

/-- The restricted fused tail retains its complete original callback interpretation under the whole owner interface. -/
theorem tail_program (work : OracleComp (PqxdhInitialFusedBeacon.Spec Response Shared) Result) :
    simulateQ (native (I := I) (D := D) (K := K) (X := X)) (simulateQ tailLift work) =
      simulateQ PqxdhBeaconPhase2Shared.tailLift (simulateQ PqxdhInitialFusedBeacon.native work) := by
  have bridge : native ∘ₛ (tailLift (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared)) =
      PqxdhBeaconPhase2Shared.tailLift ∘ₛ PqxdhInitialFusedBeacon.native := by
    funext query
    simp [QueryImpl.compose, tailLift, native, OracleSpec.query]
  rw [← QueryImpl.simulateQ_compose, bridge, QueryImpl.simulateQ_compose]

/-- The entire actual Beacon owner is recovered for every initial/inactive phase, with its original preparation, failures, complete prior state and publication behavior. -/
theorem owner_native (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : PqxdhBeaconPhase2Preparation.State I D K) :
    simulateQ (native (X := X) (Response := Response) (Shared := Shared)) (owner decode raw state) =
      PqxdhBeaconPhase2Shared.owner decode raw state := by
  unfold owner PqxdhBeaconPhase2Shared.owner
  cases phase : state.beacon.phase
  case initSent control prekey oneTime kem =>
    simp only [simulateQ_bind, pre_program]
    apply bind_congr
    intro prepared
    cases prepared with
    | none => rfl
    | some prepared =>
        simp only [simulateQ_bind, tail_program, PqxdhInitialFusedBeacon.tail_native, simulateQ_pure]
  all_goals rfl

section Post
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPrivateKemSource PqxdhKemIndCca
open PqxdhJointKdfGame PqxdhChallengeSecretRouting PqxdhPhase2SourceAux
variable {ι M P A : Type} {baseSpec : OracleSpec ι} {S B : Nat}

noncomputable def finish
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (challenge : MlKem768Ciphertext) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (PqxdhPhase2LiveFinish.FinishSpec B)
      (StateT (PqxdhPhase2PostScheduler.State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count)
        (OracleComp (LocalPostSpec baseSpec)))
  | .finish index raw => fun before => PqxdhPhase2PostScheduler.installed index before <$>
      (simulateQ (PqxdhPhase2PostScheduler.handles attachedVerify primitives count fixed localImpl challenge ∘ₛ native)
        (owner decode raw (before.1.roles.1.2 index))).run (before.1.primitive, before.2)

/-- The actual current post-root Beacon finish factors through the restricted owner and preserves its complete live-role, shared-primitive and private identity poststate on every attempt. -/
theorem finish_source
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (challenge : MlKem768Ciphertext) (decode : RawCtxReceive.FrameDecoder)
    (query : (PqxdhPhase2LiveFinish.FinishSpec B).Domain)
    (state : PqxdhPhase2PostScheduler.State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count) :
    (finish (baseSpec := baseSpec) attachedVerify primitives count fixed localImpl challenge decode query).run state =
      (PqxdhPhase2PostScheduler.targetFinish attachedVerify primitives count fixed localImpl challenge decode query).run state := by
  cases query
  simp only [finish, PqxdhPhase2PostScheduler.targetFinish, QueryImpl.simulateQ_compose, owner_native]

end Post
end BeaconcryptCore.Computational.PqxdhInitialFusedOwner

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFusedOwner.pre_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFusedOwner.pre_program

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFusedOwner.tail_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFusedOwner.tail_program

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFusedOwner.owner_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFusedOwner.owner_native

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFusedOwner.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFusedOwner.finish_source
