import BeaconcryptCore.Computational.PqxdhInitialSourceInitialSecrecy
import BeaconcryptCore.Computational.PqxdhInitialPendingCurrent
import BeaconcryptCore.Computational.PqxdhInitialCurrentBudgets

/-!
The initializer secrecy comparison is supplied by the actual authenticated-root preparation. Completed branches retain their original decision. Pending branches retain the original prepared protocol fields, private KEM interpreter and identity state, original local callbacks, complete adaptive post client and root-free source input. No established-state distribution is postulated.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialPreparedSourceInput
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily PqxdhInitialBeaconAmbient
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma
open PqxdhPhase2GeneratedDriver PqxdhAuthenticatedRootExperiment PqxdhPhase1AcceptanceOracle
open PqxdhSourceAuthenticatedRoot PqxdhPrivateAcceptedRoot PqxdhPrivateKemSource PqxdhGeneratedBeaconState
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))

abbrev Input := PqxdhInitialSourceInitialSecrecy.Input (SelectorSpec baseSpec) M P
  (PqxdhGeneratedBeaconState.IdentityHandle I) (DhPair setup) (PqxdhGeneratedBeaconState.KemHandle K)
  (X ⊕ PqxdhPhase2JointIdentity.Converted) Response A (BareState 1) S (B + 1)

noncomputable def other (secret : KemSK) (challenge : MlKem768Ciphertext) :
    QueryImpl (PqxdhInitialNativeLog.External (SelectorSpec baseSpec) RatchetChain
      (PqxdhGeneratedBeaconState.IdentityHandle I) (DhPair setup) (PqxdhGeneratedBeaconState.KemHandle K)
      (X ⊕ PqxdhPhase2JointIdentity.Converted) Response PqxdhPhase2DecapsulationRouting.Shared)
      (Ambient A (BareState 1) RootOracle.QueryCache)
  | .inl query => PqxdhInitialCurrentBeacon.preparation attachedVerify primitives 1 env.source env.localImpl baseImpl kem secret challenge query
  | .inr (.inl reply) => PqxdhInitialCurrentBeacon.application attachedVerify primitives 1 env.source env.localImpl baseImpl kem secret challenge reply
  | .inr (.inr (.inl _)) => pure none
  | .inr (.inr (.inr (.inl query))) => PqxdhInitialPendingAmbient.selectorLift
      (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem secret challenge) query
  | .inr (.inr (.inr (.inr query))) => lift (env.aux query)

noncomputable def input
    (context : PqxdhInitialLegalObserver.Context env kem attachedVerify primitives program post)
    (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64) (ancestors disclosed : List RatchetChain) :
    Bool ⊕ Input (M := M) (P := P) (I := I) (K := K) (X := X) (Response := Response) (A := A) (S := S) (B := B) (setup := setup) :=
  match context.state with
  | .completed decision => .inl decision
  | .pending prepared ephemeral =>
    let before := PqxdhInitialGenericProtocol.fromNative ConcreteRatchetKernel.refined prepared.1.context.selection.2
    .inr {
      selectedMessage := coordinates (serverCoordinates env.source.crypto env.server.ikSk ephemeral.toList
        prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.before.publicKey prepared.1.context.generated.after.publicKey)
      other := other env baseImpl kem attachedVerify primitives context.secretKey context.ciphertext
      index := env.index
      metadata := env.metadata
      ready := ready env.server env.application prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.after.publicKey
        ephemeral context.ciphertext (List.Vector.replicate 32 0)
      post := post prepared.1.context.selection.1
      before := ⟨before.roles, before.controls, before.consumed⟩
      selected := selected
      number := number
      ancestors := ancestors
      disclosed := disclosed
      shared := prepared.1.context.selection.2.primitive
      privateState := prepared.2
      cache := ∅ }

noncomputable def prior (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64) (ancestors disclosed : List RatchetChain) :=
  (fun context => input env baseImpl kem attachedVerify primitives program post context selected number ancestors disclosed) <$>
    PqxdhCorrelatedExtractFamily.prepare baseImpl kem (protocol env kem attachedVerify primitives program post)

variable (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64) (ancestors disclosed : List RatchetChain)
local notation "preparedPrior" => prior env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed

noncomputable def uniformRoot : ProbComp Bool :=
  PqxdhInitialSourceInitialSecrecy.real env.source env.recordWriter env.senderId env.route env.decode preparedPrior
noncomputable def uniformInitial : ProbComp Bool :=
  PqxdhInitialSourceInitialSecrecy.random env.source env.recordWriter env.senderId env.route env.decode preparedPrior
noncomputable def joint := PqxdhInitialSourceInitialSecrecy.sampler preparedPrior
noncomputable def observer := PqxdhInitialSourceInitialSecrecy.observer
  (extra := SelectorSpec baseSpec) (P := P) (I := IdentityHandle I) (D := DhPair setup) (K := KemHandle K)
  (X := X ⊕ PqxdhPhase2JointIdentity.Converted) (Response := Response) (A := A) (N := BareState 1) (S := S) (B := B + 1)
  env.source env.recordWriter env.senderId env.route env.decode

local notation "actualJoint" => joint env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed
local notation "actualObserver" => observer env

/-- The original authenticated-root preparation supplies the exact joint sampler and the whole actual source publication/freshness observer for the coefficient-one initializer reduction. -/
theorem initial_bound (hmac : HmacSha512) (correct : SourceFullCorrect env.source hmac) :
    (uniformRoot env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed).boolDistance
      (uniformInitial env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed) ≤
      (extractRealGame hmac actualJoint (fullExtractReduction hmac .ratchet actualObserver)).boolDistance
        (extractUniformGame actualJoint (fullExtractReduction hmac .ratchet actualObserver)) +
      (hmacPrfRealGame hmac (fullExpandReduction .ratchet actualJoint actualObserver)).boolDistance
        (hmacPrfRandomGame (fullExpandReduction .ratchet actualJoint actualObserver)) := by
  exact PqxdhInitialSourceInitialSecrecy.bound env.source env.recordWriter env.senderId env.route env.decode preparedPrior hmac correct

/-- The constructed concrete source initializer reduction makes at most two ordinary HMAC challenge queries. -/
theorem hmac_queries :
    (fullExpandReduction .ratchet actualJoint actualObserver).IsQueryBoundP IsHmacChallengeQuery 2 :=
  fullExpandReduction_hmac_query_bound _ _ _

/-- The actual preparation, copied into the source input carrier, pays the source certificate's key-generation, full preparation, base/decapsulation interpretation and encapsulation bill before its independent root draw. -/
theorem joint_uniform (c : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program post) :
    (actualJoint).IsTotalQueryBound
      (c.qKeygen + ((c.uPre + c.qBase * c.bPre + c.qDecap * c.dPre) + c.qEncap) + 32) := by
  apply PqxdhInitialSourceInitialSecrecy.sampler_uniform
  apply (isQueryBound_map_iff _ _ _ _ _).2
  exact PqxdhCorrelatedExtractQueryBounds.prepare_uniform_bound baseImpl kem
    (protocol env kem attachedVerify primitives program post) _ _ _ _ _ _ _ _ _ _ _
    (PqxdhAuthenticatedRootBudgets.sampler_bounds env baseImpl kem attachedVerify primitives program post c)

end BeaconcryptCore.Computational.PqxdhInitialPreparedSourceInput

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedSourceInput.initial_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedSourceInput.initial_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedSourceInput.hmac_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedSourceInput.hmac_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedSourceInput.joint_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedSourceInput.joint_uniform
