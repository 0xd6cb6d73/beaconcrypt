import BeaconcryptCore.Computational.PqxdhAuthenticatedRootExperiment

/-!
The authenticated-root experiment uses the actual reached Server fields and native registration acceptance. The initial root-field relation describes the representation of the selected Server; the generated source scheduler proves its preservation while allowing peer maps and complete private primitive state to evolve. A successful source branch then runs the extracted acceptance, derives the root from its exact pending input, consumes its registration identifier, and invokes the native response builder before the unchanged adaptive continuation.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhAuthenticatedRootBoundary
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhPhase2GeneratedDriver PqxdhGeneratedBeaconState
open PqxdhPrivateRootSource PqxdhPrivateAcceptedRoot PqxdhKemIndCca PqxdhInitializerSecrecy
open PqxdhSourceAuthenticatedRoot PqxdhHiddenRoot PqxdhAuthenticatedRootExperiment

variable {ι : Type} {baseSpec : OracleSpec ι} {M P I K X Response A KemSK : Type} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}

/-- The same original generated source run supplies the reached Server fields, without an external scheduler-invariant assumption or an honest selected-candidate premise. -/
theorem reached_root_fields
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (secretIdentity : M → Pqxdh.Bytes)
    (initialMatch : PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity
      env.senderId env.index env.server env.initial)
    (result : Option (PqxdhPrivateCandidateAcceptance.Outcome
      (PqxdhPrivatePhase1Prefix.Retained setup KemSK (driver env.toDriverEnvironment program).State)) ×
        PqxdhPhase1AcceptanceOracle.BareState 1)
    (present : result ∈ support (PqxdhPrivateSourceCoins.privateRun attachedVerify primitives 1
      (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup (driver env.toDriverEnvironment program)))) :
    ∃ output, result.1.map PqxdhPrivateRootSource.eraseOutput = some output ∧
      PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity env.senderId env.index
        env.server output.context.selection.2 := by
  exact PqxdhPhase2GeneratedServerFields.reached_root_fields env.toDriverEnvironment program attachedVerify
    primitives 1 baseImpl kem result present secretIdentity env.index env.server initialMatch

/-- Internal target eligibility and the successful actual DH/conversion branch supply the accepted native-builder facts. -/
theorem eligible_ready_from
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (program : Program baseSpec setup.Context S (B + 1))
    (prepared : Prepared setup (driver env.toDriverEnvironment program).State)
    (ephemeral : List.Vector UInt8 32) (ciphertext : MlKem768Ciphertext) (shared : MlKemSharedSecret)
    (eligible : targetEligible env.parameters prepared = true)
    (valid : rootFailure env.source.crypto env.server.ikSk ephemeral.toList prepared.1.context.publicIdentity.ed25519
      prepared.1.context.generated.before.publicKey prepared.1.context.generated.after.publicKey = none) :
    PqxdhProtocolBranchSupport.ReadyFrom env.source env.server env.application (some prepared.1)
      (ready env.server env.application prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.after.publicKey
        ephemeral ciphertext (productionHiddenRoot env.source
          (serverCoordinates env.source.crypto env.server.ikSk ephemeral.toList prepared.1.context.publicIdentity.ed25519
            prepared.1.context.generated.before.publicKey prepared.1.context.generated.after.publicKey) shared)) := by
  have fields := of_decide_eq_true eligible
  exact ⟨_, (publicMaterial setup prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated).keyTuple,
    ephemeral, ciphertext, shared, fields.1, fields.2.2, valid, rfl⟩

/-- The eligible native continuation runs the source acceptance and original builder before exactly the same complete postchallenge schedule and retained identity state. -/
theorem nativeAccepted_source
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (secretIdentity : M → Pqxdh.Bytes) (secret : KemSK)
    (prepared : Prepared setup (driver env.toDriverEnvironment program).State)
    (related : PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity env.senderId
      env.index env.server prepared.1.context.selection.2)
    (execution : Ready)
    (admitted : PqxdhProtocolBranchSupport.ReadyFrom env.source env.server env.application (some prepared.1) execution) :
    ∃ identity keys ephemeral ciphertext shared,
      prepared.1.accepted = some (identity, keys) ∧
      nativeAccepted env baseImpl kem attachedVerify primitives program post secret prepared execution = (do
        let result ← (PqxdhProtocolNativeAcceptance.nativeAccept env.source env.recordWriter env.aux secretIdentity
          env.senderId env.index env.metadata env.application identity keys ephemeral ciphertext shared).run prepared.1.context.selection.2
        Prod.fst <$> (simulateQ (PqxdhPhase2PostScheduler.actual attachedVerify primitives 1 env.source env.localImpl
          env.recordWriter env.senderId env.route env.decode baseImpl kem secret execution.ciphertext)
          (post prepared.1.context.selection.1 result.1)).run (result.2, prepared.2)) := by
  obtain ⟨identity, keys, ephemeral, ciphertext, shared, candidate, fresh, valid, rfl⟩ := admitted
  refine ⟨identity, keys, ephemeral, ciphertext, shared, candidate, ?_⟩
  rw [nativeAccepted, PqxdhProtocolNativeAcceptance.native_accept_eq_build env.source env.recordWriter env.aux secretIdentity
    env.senderId env.index env.metadata prepared.1.context.selection.2 env.server related env.application
    identity keys ephemeral ciphertext shared fresh valid]

/-- Accepted common candidates run the same source acceptance and builder before their original unblocked adaptive scheduler. -/
theorem commonAccepted_source
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (secretIdentity : M → Pqxdh.Bytes)
    (output : PqxdhPrivateCandidateAcceptance.Outcome
      (PqxdhPrivatePhase1Prefix.Retained setup Unit (driver env.toDriverEnvironment program).State))
    (related : PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity env.senderId
      env.index env.server output.context.selection.2)
    (execution : Ready)
    (admitted : PqxdhProtocolBranchSupport.ReadyFrom env.source env.server env.application (some output) execution) :
    ∃ identity keys ephemeral ciphertext shared,
      output.accepted = some (identity, keys) ∧
      (commonObserver env program post).accepted (some output) execution = (do
        let result ← PqxdhProtocolRegistration.coins
          ((PqxdhProtocolNativeAcceptance.nativeAccept env.source env.recordWriter env.aux secretIdentity
            env.senderId env.index env.metadata env.application identity keys ephemeral ciphertext shared).run output.context.selection.2)
        simulateQ selectorLift (Prod.fst <$>
          (simulateQ (PqxdhPhase2SourceScheduler.compiler env.source env.recordWriter env.senderId env.route env.decode env.localImpl)
            (post output.context.selection.1 result.1)).run result.2)) := by
  obtain ⟨identity, keys, ephemeral, ciphertext, shared, candidate, fresh, valid, rfl⟩ := admitted
  refine ⟨identity, keys, ephemeral, ciphertext, shared, candidate, ?_⟩
  rw [commonObserver, PqxdhProtocolNativeAcceptance.native_accept_eq_build env.source env.recordWriter env.aux secretIdentity
    env.senderId env.index env.metadata output.context.selection.2 env.server related env.application
    identity keys ephemeral ciphertext shared fresh valid]

end BeaconcryptCore.Computational.PqxdhAuthenticatedRootBoundary

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootBoundary.reached_root_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootBoundary.reached_root_fields

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootBoundary.eligible_ready_from' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootBoundary.eligible_ready_from

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootBoundary.nativeAccepted_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootBoundary.nativeAccepted_source

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootBoundary.commonAccepted_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootBoundary.commonAccepted_source
