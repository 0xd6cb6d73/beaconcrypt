import BeaconcryptCore.Computational.PqxdhPhase2SharedKemHandles
import BeaconcryptCore.Computational.PqxdhPhase2PostSource
import BeaconcryptCore.Computational.PqxdhPhase2SourceScheduler
import BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot

/-!
The postchallenge scheduler keeps the original live state and the whole private identity interpreter side by side. Public delivery returns only the original optional plaintext. The native interpreter alone receives the selected KEM secret. The compiled target continuation receives the public challenge ciphertext and routes matching private root requests through the existing opaque shared-secret interface. Common and rejected candidates use a separate unblocked execution.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPhase2PostScheduler
open PqxdhPhase2SourceAux PqxdhKemIndCca PqxdhPrivateKemSource PqxdhJointKdfGame
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPhase1AcceptanceOracle
open PqxdhChallengeSecretRouting PqxdhInitializerSecrecy
open PqxdhGeneratedBeaconState (IdentityHandle KemHandle)
open PqxdhPhase2JointIdentity (Converted)
variable {ι M P I D K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}

abbrev LiveState := PqxdhPhase2SourceScheduler.State M P I D K A S B
abbrev State (count : Nat) := LiveState (M := M) (P := P) (I := I) (D := D) (K := K)
  (A := A) (S := S) (B := B) × BareState count
abbrev Spec := PqxdhPhase2SourceScheduler.Spec baseSpec S B
abbrev NativeSpec := PqxdhPhase2SourceScheduler.NativeSpec I D K X Response
abbrev SharedSpec := PqxdhBeaconPhase2Shared.FullSpec (IdentityHandle I) D (KemHandle K)
  (X ⊕ Converted) Response PqxdhPhase2DecapsulationRouting.Shared

/-- Original selected-key decapsulation is confined to this actual private interpreter. -/
noncomputable def native
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK) :
    QueryImpl (NativeSpec (I := I) (D := D) (K := K) (X := X) (Response := Response))
      (StateT (SharedState A × BareState count) ProbComp) :=
  PqxdhPhase2NativeSource.native source baseImpl kem secret
    (directAux attachedVerify primitives count source localImpl) ∘ₛ
      PqxdhPhase2KemHandles.native PqxdhPhase2KemProvenance.encode

/-- The private target compiler has no selected secret-key or shared-secret argument. -/
noncomputable def handles
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (challenge : MlKem768Ciphertext) :
    QueryImpl (SharedSpec (I := I) (D := D) (K := K) (X := X) (Response := Response))
      (StateT (SharedState A × BareState count) (OracleComp (LocalPostSpec baseSpec))) :=
  PqxdhBeaconPhase2Routed.handles source challenge
    (borrowedAux attachedVerify primitives count source localImpl) ∘ₛ
      PqxdhPhase2SharedKemHandles.full PqxdhPhase2KemProvenance.encode

/-- Whole-owner installation and the exact updated private identity state accompany the actual reply. -/
def installed {count : Nat} (index : Fin B) (before : State (M := M) (P := P) (I := I)
    (D := D) (K := K) (A := A) (S := S) (B := B) count)
    (result : (Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State (IdentityHandle I) D (KemHandle K)) ×
      (SharedState A × BareState count)) :
    Option Pqxdh.Bytes × State (M := M) (P := P) (I := I) (D := D) (K := K)
      (A := A) (S := S) (B := B) count :=
  (result.1.1, (PqxdhPhase2LiveFinish.install index before.1 result.1.2 result.2.1, result.2.2))

/-- The actual native owner executes in source order before complete installation. -/
noncomputable def nativeFinish
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (decode : RawCtxReceive.FrameDecoder) : QueryImpl (PqxdhPhase2LiveFinish.FinishSpec B)
      (StateT (State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count) ProbComp)
  | .finish index raw => fun before => installed index before <$>
      (simulateQ (native attachedVerify primitives count source localImpl baseImpl kem secret)
        (PqxdhBeaconPhase2Publication.nativeOwner decode raw (before.1.roles.1.2 index))).run
          (before.1.primitive, before.2)

/-- Opaque target processing returns the same optional API reply and retains every installed field. -/
noncomputable def targetFinish
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (challenge : MlKem768Ciphertext) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (PqxdhPhase2LiveFinish.FinishSpec B)
      (StateT (State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count)
        (OracleComp (LocalPostSpec baseSpec)))
  | .finish index raw => fun before => installed index before <$>
      (simulateQ (handles attachedVerify primitives count source localImpl challenge)
        (PqxdhBeaconPhase2Shared.owner decode raw (before.1.roles.1.2 index))).run
          (before.1.primitive, before.2)

set_option backward.isDefEq.respectTransparency false in
/-- On one good KEM sample, the original owner and every private poststate equal the compiled target execution. -/
theorem owner_actual
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some supplied))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (owner : RawCtxBeaconLifecycle.State (IdentityHandle I) D (KemHandle K))
    (state : SharedState A × BareState count) :
    (simulateQ (native attachedVerify primitives count source localImpl baseImpl kem secret)
      (PqxdhBeaconPhase2Publication.nativeOwner decode raw owner)).run state =
      simulateQ (kemAmbientImpl baseImpl) (simulateQ (actualImpl source kem secret challenge)
        ((simulateQ (handles attachedVerify primitives count source localImpl challenge)
          (PqxdhBeaconPhase2Shared.owner decode raw owner)).run state)) := by
  have direct := PqxdhPhase2PostSource.native_complete attachedVerify primitives count source localImpl
    baseImpl kem secret challenge
    (simulateQ (PqxdhPhase2KemHandles.native PqxdhPhase2KemProvenance.encode)
      (PqxdhBeaconPhase2Publication.nativeOwner decode raw owner)) state
  rw [native, QueryImpl.simulateQ_compose, ← direct]
  rw [← QueryImpl.simulateQ_compose,
    PqxdhBeaconPhase2Shared.owner_realization _ _ _
      (PqxdhPhase2SharedKemHandles.full_calls PqxdhPhase2KemProvenance.encode _ _ _
        (PqxdhBeaconPhase2Routed.full_calls source kem secret challenge supplied agreement
          (borrowedAux attachedVerify primitives count source localImpl)))]
  simpa only [handles, QueryImpl.simulateQ_compose] using
    congrArg (simulateQ (kemAmbientImpl baseImpl))
      (simulateQ_StateT_compose
        (PqxdhBeaconPhase2Routed.handles source challenge
          (borrowedAux attachedVerify primitives count source localImpl))
        (actualImpl source kem secret challenge)
        (PqxdhBeaconPhase2Routed.actualHandles source kem secret challenge
          (borrowedAux attachedVerify primitives count source localImpl))
        (fun _ _ => rfl)
        (simulateQ (PqxdhPhase2SharedKemHandles.full PqxdhPhase2KemProvenance.encode)
          (PqxdhBeaconPhase2Shared.owner decode raw owner)) state).symm

set_option backward.isDefEq.respectTransparency false in
/-- Complete native installation commutes with the same good-sample target simulation. -/
theorem finish_actual
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some supplied))
    (decode : RawCtxReceive.FrameDecoder) (query : (PqxdhPhase2LiveFinish.FinishSpec B).Domain)
    (state : State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count) :
    (nativeFinish attachedVerify primitives count source localImpl baseImpl kem secret decode query).run state =
      simulateQ (kemAmbientImpl baseImpl) (simulateQ (actualImpl source kem secret challenge)
        ((targetFinish attachedVerify primitives count source localImpl challenge decode query).run state)) := by
  cases query with
  | finish index raw =>
    simpa only [nativeFinish, targetFinish, StateT.run, simulateQ_map] using
      congrArg (Functor.map (installed index state))
        (owner_actual attachedVerify primitives count source localImpl baseImpl kem secret challenge supplied agreement
          decode raw (state.1.roles.1.2 index) (state.1.primitive, state.2))

/-- Every original public request is routed to the public CCA channel, including its challenge block. -/
def publicWork {Result : Type} (work : OracleComp (MlKemCCAOracleSpec baseSpec) Result) :
    OracleComp (LocalPostSpec baseSpec) Result := simulateQ PqxdhBeaconPhase2Routed.publicLift work

/-- The evaluated target interpreter has no effect on the public channel beyond the standard block. -/
noncomputable def interpretation (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (challenge : MlKem768Ciphertext) : QueryImpl (LocalPostSpec baseSpec) ProbComp :=
  kemAmbientImpl baseImpl ∘ₛ actualImpl source kem secret challenge

/-- Exact original public replies and their complete caller state survive interpretation. -/
theorem public_actual {Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (challenge : MlKem768Ciphertext) (work : OracleComp (MlKemCCAOracleSpec baseSpec) Result) :
    simulateQ (interpretation source baseImpl kem secret challenge) (publicWork work) =
      simulateQ (PqxdhPhase2PostSource.interpretation baseImpl kem secret challenge) work := by
  simp only [interpretation, publicWork, QueryImpl.simulateQ_compose,
    ← QueryImpl.simulateQ_compose (actualImpl source kem secret challenge) PqxdhBeaconPhase2Routed.publicLift,
    PqxdhBeaconPhase2Routed.publicLift_actual, PqxdhPhase2PostSource.interpretation]

/-- Full original public/record/reveal traffic and actual native completion share the same private state. -/
noncomputable def actual
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (senderId : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (challenge : MlKem768Ciphertext) :
    QueryImpl (Spec (baseSpec := baseSpec) (S := S) (B := B))
      (StateT (State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count) ProbComp)
  | .inl (.inl request) => fun state =>
      (fun result => (result.1, (result.2, state.2))) <$>
        (PqxdhRegistrationProtocolState.sourceImpl source writer senderId route decode request).run state.1
  | .inl (.inr request) => fun state =>
      (fun result => (result.1, (state.1, result.2))) <$>
        simulateQ (PqxdhPhase2PostSource.interpretation baseImpl kem secret challenge)
          ((borrowedSelector attachedVerify primitives count request).run state.2)
  | .inr request => nativeFinish attachedVerify primitives count source localImpl baseImpl kem secret decode request

/-- The executable target program receives no selected KEM secret or supplied shared-secret bytes. -/
noncomputable def target
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (senderId : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (challenge : MlKem768Ciphertext) :
    QueryImpl (Spec (baseSpec := baseSpec) (S := S) (B := B))
      (StateT (State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count)
        (OracleComp (LocalPostSpec baseSpec)))
  | .inl (.inl request) => fun state => publicWork (ccaCoins
      ((fun result => (result.1, (result.2, state.2))) <$>
        (PqxdhRegistrationProtocolState.sourceImpl source writer senderId route decode request).run state.1))
  | .inl (.inr request) => fun state => publicWork
      ((fun result => (result.1, (state.1, result.2))) <$>
        (borrowedSelector attachedVerify primitives count request).run state.2)
  | .inr request => targetFinish attachedVerify primitives count source localImpl challenge decode request

variable
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (senderId : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some supplied))

include supplied agreement in
set_option backward.isDefEq.respectTransparency false in
/-- Every original public reply and native completion has the same complete private state on the single good KEM sample. -/
theorem step_actual
    (query : (Spec (baseSpec := baseSpec) (S := S) (B := B)).Domain)
    (state : State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count) :
    (actual attachedVerify primitives count source localImpl writer senderId route decode baseImpl kem secret challenge query).run state =
      simulateQ (interpretation source baseImpl kem secret challenge)
        ((target attachedVerify primitives count source localImpl writer senderId route decode challenge query).run state) := by
  rcases query with (query | query)
  · cases query with
    | inl request =>
      simp only [actual, target, StateT.run, public_actual, PqxdhPhase2PostSource.coins]
    | inr request =>
      simp only [actual, target, StateT.run, public_actual, simulateQ_map]
  · simpa only [actual, target, interpretation, QueryImpl.simulateQ_compose] using
      finish_actual attachedVerify primitives count source localImpl baseImpl kem secret challenge supplied agreement decode query state

include supplied agreement in
/-- The entire adaptive postchallenge execution agrees, including all replies, complete live owners, caches and identity history. -/
theorem schedule_actual {Result : Type}
    (client : OracleComp (Spec (baseSpec := baseSpec) (S := S) (B := B)) Result)
    (state : State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count) :
    (simulateQ (actual attachedVerify primitives count source localImpl writer senderId route decode baseImpl kem secret challenge) client).run state =
      simulateQ (interpretation source baseImpl kem secret challenge)
        ((simulateQ (target attachedVerify primitives count source localImpl writer senderId route decode challenge) client).run state) := by
  exact (simulateQ_StateT_compose
    (target attachedVerify primitives count source localImpl writer senderId route decode challenge)
    (interpretation source baseImpl kem secret challenge)
    (actual attachedVerify primitives count source localImpl writer senderId route decode baseImpl kem secret challenge)
    (fun query before => (step_actual attachedVerify primitives count source localImpl writer senderId route decode
      baseImpl kem secret challenge supplied agreement query before).symm) client state).symm

include supplied agreement in
/-- The same single good KEM sample also routes every matching private root through the one supplied secret. No second correctness event is introduced. -/
theorem schedule_reduction {Result : Type}
    (client : OracleComp (Spec (baseSpec := baseSpec) (S := S) (B := B)) Result)
    (state : State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count) :
    (simulateQ (actual attachedVerify primitives count source localImpl writer senderId route decode baseImpl kem secret challenge) client).run state =
      simulateQ (kemAmbientImpl baseImpl) (simulateQ (publicImpl kem secret challenge)
        (simulateQ (PqxdhChallengeSecretRouting.route source challenge supplied)
          ((simulateQ (target attachedVerify primitives count source localImpl writer senderId route decode challenge) client).run state))) := by
  rw [schedule_actual attachedVerify primitives count source localImpl writer senderId route decode baseImpl kem secret challenge supplied agreement,
    route_complete source kem secret challenge supplied agreement]
  exact QueryImpl.simulateQ_compose _ _ _

end BeaconcryptCore.Computational.PqxdhPhase2PostScheduler

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PostScheduler.owner_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PostScheduler.owner_actual

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PostScheduler.finish_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PostScheduler.finish_actual

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PostScheduler.public_actual' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PostScheduler.public_actual

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PostScheduler.step_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PostScheduler.step_actual

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PostScheduler.schedule_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PostScheduler.schedule_actual

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PostScheduler.schedule_reduction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PostScheduler.schedule_reduction
