import BeaconcryptCore.Computational.PqxdhProtocolExperiment
import BeaconcryptCore.Computational.PqxdhProtocolBranchSupport

/-!
The source-side native acceptance operation retains the complete original pending token and derives its root from that token's exact input bytes before inserting the consumed registration ID. It then runs the original native response builder against the reached role state. The private KEM shared secret is an input to this source interpreter only. The equivalent accepted-root reduction continuation still receives only its original Ready value; no shared-secret field is added to that interface.

The equality assumes the explicit stored-Server root-field relation. Freshness and successful conversion/DH are actual branch facts, derived by PqxdhProtocolBranchSupport rather than new security assumptions. Fixed HKDF is total on the legal source input under its primitive contract; allocation capacity effects and native consumed-HashSet representation remain external to this logical state. Diagnostic extracted failures stay diagnostic.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhProtocolNativeAcceptance
open PqxdhEd25519EufCma PqxdhKemIndCca PqxdhSourceAuthenticatedRoot PqxdhHiddenRoot
open PqxdhPrivateAcceptedRoot PqxdhProtocolExperiment

variable {M P I D K A : Type} {S B : Nat}

/-- Source root derivation reads the actual pending input before source consumption. -/
def nativeRoot (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (pending : pqxdh.PendingServerRegistration) : PqxdhSecretInputKdf.RootOutput :=
  ⟨Pqxdh.rootSecret source.crypto (PqxdhRefinement.absBytes pending.root_key_input.bytes),
    Pqxdh.rootSecret_length source.crypto _⟩

/-- Actual typed acceptance, root derivation, RID consumption and response execution retain the complete reached native state. -/
noncomputable def nativeAccept
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (secretIdentity : M → Pqxdh.Bytes) (senderId : M → Std.U64) (index : Fin S) (metadata : P)
    (application : Option Pqxdh.Bytes) (identity : Ed25519PublicKey) (keys : Phase1KeyTuple)
    (ephemeral : List.Vector UInt8 32) (ciphertext : MlKem768Ciphertext) (secret : MlKemSharedSecret) :
    StateT (PqxdhRegistrationProtocolState.State M P I D K A S B) ProbComp
      (RustM (Option PqxdhServerRegistrationPublication.Response)) := fun state =>
  match PqxdhProtocolAcceptance.accept source.crypto secretIdentity senderId index metadata state
    identity keys ephemeral ciphertext secret with
  | .ok (.Ok (_, pending)) =>
      (PqxdhRegistrationProtocolState.nativeBuild source writer aux senderId index metadata pending
        (nativeRoot source pending) application).run
          { state with
            consumed := Function.update state.consumed index
              (PqxdhRefinement.absBytes pending.registration_id.bytes :: state.consumed index) }
  | .ok (.Err _) => pure (.ok none, state)
  | .fail error => pure (.fail error, state)
  | .div => pure (.div, state)

/-- The actual accepted-source execution equals the private reduction's existing root callback, retaining all result and state effects. -/
theorem native_accept_eq_build
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (secretIdentity : M → Pqxdh.Bytes) (senderId : M → Std.U64) (index : Fin S) (metadata : P)
    (state : PqxdhRegistrationProtocolState.State M P I D K A S B) (server : Pqxdh.ServerState)
    (related : PqxdhProtocolServerInvariant.RootFields source.crypto secretIdentity senderId index server state)
    (application : Option Pqxdh.Bytes) (identity : Ed25519PublicKey) (keys : Phase1KeyTuple)
    (ephemeral : List.Vector UInt8 32) (ciphertext : MlKem768Ciphertext) (secret : MlKemSharedSecret)
    (fresh : identity.toList ++ keys.oneTime.toList ∉ server.consumed)
    (valid : rootFailure source.crypto server.ikSk ephemeral.toList identity keys.prekey keys.oneTime = none) :
    (nativeAccept source writer aux secretIdentity senderId index metadata application identity keys ephemeral ciphertext secret).run state =
      (PqxdhRegistrationProtocolState.build source writer aux senderId index metadata
        (ready server application identity keys.oneTime ephemeral ciphertext
          (productionHiddenRoot source (serverCoordinates source.crypto server.ikSk ephemeral.toList identity keys.prekey keys.oneTime) secret))).run state := by
  obtain ⟨pending, accepted, rootBytes, _, builder⟩ := PqxdhProtocolAcceptance.accepted_builder
    source writer aux secretIdentity senderId index metadata state server related application identity keys ephemeral ciphertext secret
    (productionHiddenRoot source (serverCoordinates source.crypto server.ikSk ephemeral.toList identity keys.prekey keys.oneTime) secret)
    fresh valid
  rw [builder]
  simp only [nativeAccept, StateT.run, accepted, nativeRoot, rootBytes, productionHiddenRoot]

variable {ι : Type} {baseSpec : OracleSpec ι}

/-- The successful facts derived by the actual source branch run the original core acceptance and root derivation before the same adaptive continuation. -/
theorem accepted_native_run (env : Environment baseSpec M P I D K A S B)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec)
    (program : PqxdhProtocolSelector.Program baseSpec setup.Context S B) (post : Post program.Selection S B)
    (secretIdentity : M → Pqxdh.Bytes)
    (output : PqxdhProtocolRegistration.Output (M := M) (P := P) (I := I) (D := D) (K := K)
      (A := A) (S := S) (B := B) setup program.Selection)
    (related : PqxdhProtocolServerInvariant.RootFields env.parameters.source.crypto secretIdentity env.senderId
      env.index env.parameters.server (PqxdhProtocolRegistration.reached env.initial output))
    (execution : Ready)
    (admitted : PqxdhProtocolBranchSupport.ReadyFrom env.parameters.source env.parameters.server
      env.parameters.application output execution) :
    ∃ identity keys ephemeral ciphertext secret,
      output.bind (·.accepted) = some (identity, keys) ∧
      execution = ready env.parameters.server env.parameters.application identity keys.oneTime ephemeral ciphertext
        (productionHiddenRoot env.parameters.source (serverCoordinates env.parameters.source.crypto
          env.parameters.server.ikSk ephemeral.toList identity keys.prekey keys.oneTime) secret) ∧
      (env.observer setup program post).accepted output execution = PqxdhProtocolRegistration.coins (do
        let result ← (nativeAccept env.parameters.source env.writer env.aux secretIdentity env.senderId env.index env.metadata
          env.parameters.application identity keys ephemeral ciphertext secret).run
            (PqxdhProtocolRegistration.reached env.initial output)
        Prod.fst <$> (simulateQ (PqxdhRegistrationProtocolState.sourceImpl env.parameters.source env.writer env.senderId
          env.route env.decode) (post (PqxdhProtocolRegistration.choice output) result.1)).run result.2) := by
  obtain ⟨identity, keys, ephemeral, ciphertext, secret, candidate, fresh, valid, rfl⟩ := admitted
  refine ⟨identity, keys, ephemeral, ciphertext, secret, candidate, rfl, ?_⟩
  rw [Environment.observer, Environment.plan, PqxdhProtocolRegistration.accepted_run,
    native_accept_eq_build env.parameters.source env.writer env.aux secretIdentity env.senderId env.index env.metadata
      (PqxdhProtocolRegistration.reached env.initial output) env.parameters.server related env.parameters.application
      identity keys ephemeral ciphertext secret fresh valid]

end BeaconcryptCore.Computational.PqxdhProtocolNativeAcceptance

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolNativeAcceptance.native_accept_eq_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolNativeAcceptance.native_accept_eq_build

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolNativeAcceptance.accepted_native_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolNativeAcceptance.accepted_native_run
