import BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot

/-!
Actual source branch congruence retains the original optional verification result, fresh registration identifier and successful conversion/DH test before the private accepted-root continuation. It preserves the entire OracleComp program, including all source draws and callback state interpretation. This is an operational law for the fixed functional source, not an authentication or native allocation/optional-HKDF theorem.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhProtocolBranchSupport
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhJointIdentityFamily PqxdhJointIdentityFreshness
open PqxdhJointPhase1SourceWriter PqxdhJointPhase1AcceptanceComposition
open PqxdhPhase1AcceptanceOracle PqxdhPrivateSourceCoins PqxdhPrivateCandidateAcceptance
open PqxdhPrivateKemSource PqxdhPrivatePhase1Prefix
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhStatefulPhase1EufCma
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhSecretInputInitializer
open PqxdhSourceAuthenticatedRoot PqxdhHiddenRoot PqxdhPrivateRootSource
open PqxdhChallengeSecretRouting PqxdhPrivateAcceptedRoot

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

/-- Actual candidate fields and the successful source branch determine every accepted root input. -/
def ReadyFrom {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (output : Option (Outcome Context)) (execution : Ready) : Prop :=
  ∃ identity keys ephemeral ciphertext secret,
    output.bind (·.accepted) = some (identity, keys) ∧
    identity.toList ++ keys.oneTime.toList ∉ server.consumed ∧
    rootFailure source.crypto server.ikSk ephemeral.toList identity keys.prekey keys.oneTime = none ∧
    execution = ready server application identity keys.oneTime ephemeral ciphertext
      (productionHiddenRoot source
        (serverCoordinates source.crypto server.ikSk ephemeral.toList identity keys.prekey keys.oneTime) secret)

theorem observe_congr
    (source : FixedHkdfSha512NoSaltSource) (challenge : Option MlKem768Ciphertext)
    (verify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (setup : StatefulPhase1Setup baseSpec) {Selection : Type}
    (left right : Continuation setup Selection) (output : Option (Outcome (Retained setup Unit Selection)))
    (execution : ServerExecution) (state : BareState count)
    (same : left.completed output execution = right.completed output execution) :
    PqxdhPrivateAcceptedRoot.observe source challenge verify primitives count setup left output execution state =
      PqxdhPrivateAcceptedRoot.observe source challenge verify primitives count setup right output execution state := by
  simp only [PqxdhPrivateAcceptedRoot.observe, localObserve, same]

theorem acceptedObserve_congr
    (source : FixedHkdfSha512NoSaltSource) (challenge : Option MlKem768Ciphertext)
    (verify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (setup : StatefulPhase1Setup baseSpec) {Selection : Type}
    (left right : Continuation setup Selection) (output : Option (Outcome (Retained setup Unit Selection)))
    (execution : Ready) (state : BareState count)
    (same : left.accepted output execution = right.accepted output execution) :
    acceptedObserve source challenge verify primitives count setup left output execution state =
      acceptedObserve source challenge verify primitives count setup right output execution state := by
  simp only [acceptedObserve, localAccepted, same]

theorem targetAfterEncapsulation_congr
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (verify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type}
    (left right : Continuation setup Selection) (prepared : Prepared setup Selection)
    (ephemeral : List.Vector UInt8 32) (encapsulated : Option (MlKem768Ciphertext × MlKemSharedSecret))
    (eligible : targetEligible parameters prepared = true)
    (completed : ∀ execution, execution.outcome.2 = parameters.server →
      left.completed (some prepared.1) execution = right.completed (some prepared.1) execution)
    (accepted : ∀ execution,
      ReadyFrom parameters.source parameters.server parameters.application (some prepared.1) execution →
      left.accepted (some prepared.1) execution = right.accepted (some prepared.1) execution) :
    PqxdhPrivateAcceptedRoot.targetAfterEncapsulation kem parameters verify primitives setup left
      prepared ephemeral encapsulated =
    PqxdhPrivateAcceptedRoot.targetAfterEncapsulation kem parameters verify primitives setup right
      prepared ephemeral encapsulated := by
  cases encapsulated with
  | none => exact observe_congr _ _ _ _ _ _ _ _ _ _ _ (completed _ rfl)
  | some pair =>
      simp only [PqxdhPrivateAcceptedRoot.targetAfterEncapsulation]
      cases valid : rootFailure parameters.source.crypto parameters.server.ikSk ephemeral.toList
          prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.before.publicKey
          prepared.1.context.generated.after.publicKey with
      | some failure => exact observe_congr _ _ _ _ _ _ _ _ _ _ _ (completed _ rfl)
      | none =>
          apply acceptedObserve_congr
          apply accepted
          have fields := of_decide_eq_true eligible
          exact ⟨_, (publicMaterial setup prepared.1.context.publicIdentity.ed25519
            prepared.1.context.generated).keyTuple, ephemeral, pair.1, pair.2,
            fields.1, fields.2.2, valid, rfl⟩

theorem acceptedCommon_congr
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (native : PqxdhOptionalKemSource.SourceKemInterface baseSpec)
    (verify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (setup : StatefulPhase1Setup baseSpec) {Selection : Type}
    (left right : Continuation setup Selection) (output : Option (Outcome (Retained setup Unit Selection)))
    (state : BareState count) (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (identity : Ed25519PublicKey) (keys : Phase1KeyTuple)
    (candidate : output.bind (·.accepted) = some (identity, keys))
    (completed : ∀ execution, execution.outcome.2 = server →
      left.completed output execution = right.completed output execution)
    (accepted : ∀ execution, ReadyFrom source server application output execution →
      left.accepted output execution = right.accepted output execution) :
    PqxdhPrivateAcceptedRoot.acceptedCommon source kem native verify primitives count setup left output
      state server application ephemeralGen identity keys =
    PqxdhPrivateAcceptedRoot.acceptedCommon source kem native verify primitives count setup right output
      state server application ephemeralGen identity keys := by
  unfold PqxdhPrivateAcceptedRoot.acceptedCommon
  split
  · exact observe_congr _ _ _ _ _ _ _ _ _ _ _ (completed _ rfl)
  · rename_i fresh
    apply bind_congr
    intro ephemeral
    apply bind_congr
    intro encapsulated
    cases encapsulated with
    | none => exact observe_congr _ _ _ _ _ _ _ _ _ _ _ (completed _ rfl)
    | some pair =>
        cases valid : rootFailure source.crypto server.ikSk ephemeral.toList identity keys.prekey keys.oneTime with
        | some failure => exact observe_congr _ _ _ _ _ _ _ _ _ _ _ (completed _ rfl)
        | none =>
            apply acceptedObserve_congr
            exact accepted _ ⟨identity, keys, ephemeral, pair.1, pair.2, candidate, fresh, valid, rfl⟩

theorem allCandidateCommon_congr
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (native : PqxdhOptionalKemSource.SourceKemInterface baseSpec)
    (verify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (setup : StatefulPhase1Setup baseSpec) {Selection : Type}
    (left right : Continuation setup Selection) (output : Option (Outcome (Retained setup Unit Selection)))
    (state : BareState count) (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (completed : ∀ execution, execution.outcome.2 = server →
      left.completed output execution = right.completed output execution)
    (accepted : ∀ execution, ReadyFrom source server application output execution →
      left.accepted output execution = right.accepted output execution) :
    PqxdhPrivateAcceptedRoot.allCandidateCommon source kem native verify primitives count setup left
      output state server application ephemeralGen =
    PqxdhPrivateAcceptedRoot.allCandidateCommon source kem native verify primitives count setup right
      output state server application ephemeralGen := by
  unfold PqxdhPrivateAcceptedRoot.allCandidateCommon
  cases candidate : output.bind (·.accepted) with
  | none => exact observe_congr _ _ _ _ _ _ _ _ _ _ _ (completed _ rfl)
  | some pair =>
      exact acceptedCommon_congr source kem native verify primitives count setup left right output
        state server application ephemeralGen pair.1 pair.2 candidate completed accepted

/-- Every actual source branch permits callback replacement using only unchanged rejection state or its derived successful candidate facts. -/
theorem nativeNext_congr
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (verify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) {Selection : Type}
    (left right : Continuation setup Selection) (prepared : Prepared setup Selection)
    (completed : ∀ execution, execution.outcome.2 = parameters.server →
      left.completed (some prepared.1) execution = right.completed (some prepared.1) execution)
    (accepted : ∀ execution,
      ReadyFrom parameters.source parameters.server parameters.application (some prepared.1) execution →
      left.accepted (some prepared.1) execution = right.accepted (some prepared.1) execution) :
    PqxdhPrivateAcceptedRoot.nativeNext kem parameters verify primitives setup left prepared =
      PqxdhPrivateAcceptedRoot.nativeNext kem parameters verify primitives setup right prepared := by
  unfold PqxdhPrivateAcceptedRoot.nativeNext
  split
  · rename_i eligible
    unfold PqxdhPrivateAcceptedRoot.nativeTargetContinuation
    apply bind_congr
    intro ephemeral
    apply bind_congr
    intro encapsulated
    exact targetAfterEncapsulation_congr kem parameters verify primitives setup left right prepared
      ephemeral encapsulated eligible completed accepted
  · exact allCandidateCommon_congr parameters.source kem parameters.native verify primitives 1 setup
      left right (some prepared.1) prepared.2 parameters.server parameters.application
      parameters.ephemeralGen completed accepted

end BeaconcryptCore.Computational.PqxdhProtocolBranchSupport

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolBranchSupport.observe_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolBranchSupport.observe_congr

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolBranchSupport.acceptedObserve_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolBranchSupport.acceptedObserve_congr

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolBranchSupport.targetAfterEncapsulation_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolBranchSupport.targetAfterEncapsulation_congr

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolBranchSupport.acceptedCommon_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolBranchSupport.acceptedCommon_congr

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolBranchSupport.allCandidateCommon_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolBranchSupport.allCandidateCommon_congr

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolBranchSupport.nativeNext_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolBranchSupport.nativeNext_congr
