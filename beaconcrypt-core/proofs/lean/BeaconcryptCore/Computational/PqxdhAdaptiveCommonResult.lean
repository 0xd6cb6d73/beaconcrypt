import BeaconcryptCore.Computational.PqxdhAdaptiveTargetPost

/-!
The original all-candidate continuation can retain a final adversary result before observing its Boolean projection. Every native replay, encapsulation, conversion, DH and rejection branch is unchanged. Exact mapping laws recover the maintained Boolean source continuation; this adds no adversarial query or cryptographic assumption.
-/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhAdaptiveCommonResult
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhJointPhase1SourceWriter PqxdhJointPhase1AcceptanceComposition
open PqxdhPhase1AcceptanceOracle PqxdhPrivateSourceCoins PqxdhPrivateCandidateAcceptance
open PqxdhPrivateKemSource PqxdhPrivatePhase1Prefix PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhStatefulPhase1EufCma
open PqxdhJointKdfGame PqxdhHiddenRoot PqxdhSecretInputKdf PqxdhSourceAuthenticatedRoot PqxdhPrivateRootSource
open PqxdhPrivateAcceptedRoot (Ready ready CorrelatedSpec sourcePost localSourceImpl)
variable {ι Result Selection : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

structure Continuation (setup : StatefulPhase1Setup baseSpec) (Selection Result : Type) where
  completed : Option (Outcome (Retained setup Unit Selection)) → ServerExecution → OracleComp (CorrelatedSpec baseSpec) Result
  accepted : Option (Outcome (Retained setup Unit Selection)) → Ready → OracleComp (CorrelatedSpec baseSpec) Result

def project {setup : StatefulPhase1Setup baseSpec} (observer : Continuation setup Selection Result) (observe : Result → Bool) :
    PqxdhPrivateAcceptedRoot.Continuation setup Selection where
  completed output execution := observe <$> observer.completed output execution
  accepted output execution := observe <$> observer.accepted output execution

noncomputable def observe (source : FixedHkdfSha512NoSaltSource) (challenge : Option MlKem768Ciphertext)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives) (count : Nat)
    (setup : StatefulPhase1Setup baseSpec) (observer : Continuation setup Selection Result)
    (output : Option (Outcome (Retained setup Unit Selection))) (execution : ServerExecution) (state : BareState count) :
    OracleComp (MlKemCCAOracleSpec baseSpec) Result :=
  simulateQ (sourcePost source challenge) (Prod.fst <$>
    (simulateQ (localSourceImpl source attachedVerify primitives count) (observer.completed output execution)).run state)

/-- Projecting the returned result after the complete original failed/common continuation recovers exactly the maintained Boolean observer. -/
theorem observe_map (source : FixedHkdfSha512NoSaltSource) (challenge : Option MlKem768Ciphertext)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives) (count : Nat)
    (setup : StatefulPhase1Setup baseSpec) (observer : Continuation setup Selection Result) (f : Result → Bool)
    (output : Option (Outcome (Retained setup Unit Selection))) (execution : ServerExecution) (state : BareState count) :
    PqxdhPrivateAcceptedRoot.observe source challenge attachedVerify primitives count setup (project observer f) output execution state =
      f <$> observe source challenge attachedVerify primitives count setup observer output execution state := by
  simp only [PqxdhPrivateAcceptedRoot.observe, PqxdhPrivateAcceptedRoot.localObserve, project, observe,
    simulateQ_map, StateT.run_map, Functor.map_map]

noncomputable def acceptedObserve (source : FixedHkdfSha512NoSaltSource) (challenge : Option MlKem768Ciphertext)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives) (count : Nat)
    (setup : StatefulPhase1Setup baseSpec) (observer : Continuation setup Selection Result)
    (output : Option (Outcome (Retained setup Unit Selection))) (execution : Ready) (state : BareState count) :
    OracleComp (MlKemCCAOracleSpec baseSpec) Result :=
  simulateQ (sourcePost source challenge) (Prod.fst <$>
    (simulateQ (localSourceImpl source attachedVerify primitives count) (observer.accepted output execution)).run state)

/-- The actual accepted common path retains its complete private state until the same final result projection. -/
theorem acceptedObserve_map (source : FixedHkdfSha512NoSaltSource) (challenge : Option MlKem768Ciphertext)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives) (count : Nat)
    (setup : StatefulPhase1Setup baseSpec) (observer : Continuation setup Selection Result) (f : Result → Bool)
    (output : Option (Outcome (Retained setup Unit Selection))) (execution : Ready) (state : BareState count) :
    PqxdhPrivateAcceptedRoot.acceptedObserve source challenge attachedVerify primitives count setup (project observer f) output execution state =
      f <$> acceptedObserve source challenge attachedVerify primitives count setup observer output execution state := by
  simp only [PqxdhPrivateAcceptedRoot.acceptedObserve, PqxdhPrivateAcceptedRoot.localAccepted, project, acceptedObserve,
    simulateQ_map, StateT.run_map, Functor.map_map]

noncomputable def acceptedCommon
    (source : FixedHkdfSha512NoSaltSource)
    (_kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (native : PqxdhOptionalKemSource.SourceKemInterface baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (setup : StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : Continuation setup Selection Result) (output : Option (Outcome (Retained setup Unit Selection)))
    (state : BareState count) (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) : OracleComp (MlKemCCAOracleSpec baseSpec) Result := do
  if identity.toList ++ keys.oneTime.toList ∈ server.consumed then
    observe source none attachedVerify primitives count setup observer output
      ⟨none, none, .error .registrationReplay, server⟩ state
  else
    let ephemeral ← OracleComp.liftComp ephemeralGen (MlKemCCAOracleSpec baseSpec)
    let encapsulated ← OracleComp.liftComp (native.encaps keys.pqKey) (MlKemCCAOracleSpec baseSpec)
    match encapsulated with
    | none =>
        observe source none attachedVerify primitives count setup observer output
          ⟨some ephemeral, none, .error .badEncoding, server⟩ state
    | some (ciphertext, secret) =>
        match rootFailure source.crypto server.ikSk ephemeral.toList identity keys.prekey keys.oneTime with
        | some failure =>
            observe source none attachedVerify primitives count setup observer output
              ⟨some ephemeral, some ciphertext, .error failure, server⟩ state
        | none =>
            acceptedObserve source none attachedVerify primitives count setup observer output
              (ready server application identity keys.oneTime ephemeral ciphertext
                (productionHiddenRoot source
                  (serverCoordinates source.crypto server.ikSk ephemeral.toList identity keys.prekey keys.oneTime) secret)) state

/-- Source replay, optional encapsulation and root-validation branches commute with only the final observer projection. -/
theorem acceptedCommon_map
    (source : FixedHkdfSha512NoSaltSource) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (native : PqxdhOptionalKemSource.SourceKemInterface baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives) (count : Nat)
    (setup : StatefulPhase1Setup baseSpec) (observer : Continuation setup Selection Result) (f : Result → Bool)
    (output : Option (Outcome (Retained setup Unit Selection))) (state : BareState count)
    (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32))
    (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) :
    PqxdhPrivateAcceptedRoot.acceptedCommon source kem native attachedVerify primitives count setup (project observer f) output state server application ephemeralGen identity keys =
      f <$> acceptedCommon source kem native attachedVerify primitives count setup observer output state server application ephemeralGen identity keys := by
  simp only [PqxdhPrivateAcceptedRoot.acceptedCommon, acceptedCommon]
  split <;> simp_all only [observe_map, map_bind]
  apply bind_congr
  intro ephemeral
  apply bind_congr
  intro encapsulated
  cases encapsulated with
  | none => rfl
  | some pair =>
    rcases pair with ⟨ciphertext, secret⟩
    cases failure : rootFailure source.crypto server.ikSk ephemeral.toList identity keys.prekey keys.oneTime <;>
      simp only [acceptedObserve_map]

noncomputable def allCandidateCommon
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (native : PqxdhOptionalKemSource.SourceKemInterface baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (setup : StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : Continuation setup Selection Result) (output : Option (Outcome (Retained setup Unit Selection)))
    (state : BareState count) (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32)) :
    OracleComp (MlKemCCAOracleSpec baseSpec) Result :=
  match output.bind (·.accepted) with
  | none => observe source none attachedVerify primitives count setup observer output
      ⟨none, none, .error .badEncoding, server⟩ state
  | some (identity, keys) => acceptedCommon source kem native attachedVerify primitives count setup observer output
      state server application ephemeralGen identity keys

/-- The same optional source acceptance keeps attacker-owned candidates, changed candidates and all rejection paths before the final target observation. -/
theorem allCandidateCommon_map
    (source : FixedHkdfSha512NoSaltSource) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (native : PqxdhOptionalKemSource.SourceKemInterface baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives) (count : Nat)
    (setup : StatefulPhase1Setup baseSpec) (observer : Continuation setup Selection Result) (f : Result → Bool)
    (output : Option (Outcome (Retained setup Unit Selection))) (state : BareState count)
    (server : Pqxdh.ServerState) (application : Option Pqxdh.Bytes)
    (ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32)) :
    PqxdhPrivateAcceptedRoot.allCandidateCommon source kem native attachedVerify primitives count setup (project observer f) output state server application ephemeralGen =
      f <$> allCandidateCommon source kem native attachedVerify primitives count setup observer output state server application ephemeralGen := by
  cases accepted : output.bind (·.accepted) <;>
    simp only [PqxdhPrivateAcceptedRoot.allCandidateCommon, allCandidateCommon, accepted, observe_map, acceptedCommon_map]

end BeaconcryptCore.Computational.PqxdhAdaptiveCommonResult

/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveCommonResult.observe_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveCommonResult.observe_map
/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveCommonResult.acceptedObserve_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveCommonResult.acceptedObserve_map
/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveCommonResult.acceptedCommon_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveCommonResult.acceptedCommon_map
/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveCommonResult.allCandidateCommon_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveCommonResult.allCandidateCommon_map
