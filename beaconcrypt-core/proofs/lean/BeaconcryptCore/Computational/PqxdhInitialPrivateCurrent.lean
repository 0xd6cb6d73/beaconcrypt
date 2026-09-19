import BeaconcryptCore.Computational.PqxdhInitialPrivateBuilder
import BeaconcryptCore.Computational.PqxdhInitialPrivateBeacon
import BeaconcryptCore.Computational.PqxdhInitialCurrentSecrecy

/-!
The current authenticated-root initializer endpoint exposes one private record-KDF interpreter before the original Server first send, through the actual Beacon initial receive, and throughout the complete original post scheduler. It retains the source initializer callback position, repeated private initializers, all actual role/control/shared state and the real public backend. The real handler recovers the exact current endpoint.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialPrivateCurrent
open PqxdhJointKdfGame PqxdhKemIndCca PqxdhCorrelatedExpand PqxdhCorrelatedExpandHybrid
open PqxdhCorrelatedExtractFamily PqxdhInitializerSecrecy PqxdhChallengeSecretRouting
open PqxdhPhase2SourceAux PqxdhPhase1AcceptanceOracle PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPrivateKemSource
open PqxdhInitialRootLabelService PqxdhSecretInputKdf
variable {ι M P I D K X Response A KemSK Result : Type} {baseSpec : OracleSpec ι} {S B : Nat}

open PqxdhAuthenticatedRootExperiment PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhSourceAuthenticatedRoot PqxdhPrivateAcceptedRoot

noncomputable def accepted {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (secret : KemSK) (selected : Message)
    (prepared : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State)
    (ready : Ready) : OracleComp PqxdhInitialLabelCompiler.Spec Bool := do
  let result ← PqxdhInitialPrivateBuilder.build env.source env.recordWriter kdf env.aux env.senderId env.index env.metadata selected ready prepared.1.context.selection.2
  Prod.fst <$> (simulateQ (PqxdhInitialPrivateBeacon.target attachedVerify primitives 1 env.source kdf env.localImpl
    env.recordWriter env.senderId env.route env.decode baseImpl kem secret ready.ciphertext)
    (post prepared.1.context.selection.1 result.1)).run (result.2, prepared.2)


/-- The full accepted current endpoint specializes exactly to the original legal observer when private derivations use the actual source function. -/
theorem accepted_source {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (secret : KemSK) (selected : Message)
    (prepared : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State)
    (ready : Ready) :
    accepted env (RawCtxSourceHkdf.kdfImpl env.source) baseImpl kem attachedVerify primitives program post secret selected prepared ready =
      PqxdhInitialLegalObserver.accepted env baseImpl kem attachedVerify primitives program post secret selected prepared ready := by
  simp only [accepted, PqxdhInitialLegalObserver.accepted, PqxdhInitialPrivateBuilder.build_source,
    PqxdhInitialPrivateBeacon.target_source]

noncomputable def acceptedDecision {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (secret : KemSK) (selected : Message)
    (prepared : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State)
    (ready : Ready) (response : PqxdhInitialRootLabelService.Response) : ProbComp Bool :=
  (simulateQ (labelledFull env.source (QueryImpl.ofLift unifSpec ProbComp) selected response)
    (accepted env kdf baseImpl kem attachedVerify primitives program post secret selected prepared ready)).run' ∅


noncomputable def observe {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (context : PqxdhInitialLegalObserver.Context env kem attachedVerify primitives program post)
    (response : PqxdhInitialRootLabelService.Response) : ProbComp Bool :=
  match context.state with
  | .completed decision => pure decision
  | .pending prepared ephemeral =>
      let selected := coordinates (serverCoordinates env.source.crypto env.server.ikSk ephemeral.toList
        prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.before.publicKey prepared.1.context.generated.after.publicKey)
      acceptedDecision env kdf baseImpl kem attachedVerify primitives program post context.secretKey selected prepared
        (ready env.server env.application prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.after.publicKey
          ephemeral context.ciphertext (List.Vector.replicate 32 0)) response


/-- The entire actual prepared-context initializer observer is recovered at the source private interpreter, including completed and pending modes. -/
theorem observe_source {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (context : PqxdhInitialLegalObserver.Context env kem attachedVerify primitives program post)
    (response : PqxdhInitialRootLabelService.Response) :
    observe env (RawCtxSourceHkdf.kdfImpl env.source) baseImpl kem attachedVerify primitives program post context response =
      PqxdhInitialLegalObserver.observe env baseImpl kem attachedVerify primitives program post context response := by
  cases mode : context.state <;> simp only [observe, PqxdhInitialLegalObserver.observe, mode, acceptedDecision,
    PqxdhInitialLegalObserver.acceptedDecision, accepted_source]

/-- The supplied initializer endpoint runs the original complete Server builder with the private handler before its FIRST send, then every actual adaptive post request through that SAME handler and the shared initializer cache. -/
theorem accepted_response {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (secret : KemSK) (selected : Message)
    (prepared : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State)
    (ready : Ready) (response : PqxdhInitialRootLabelService.Response) (cache : RootOracle.QueryCache) :
    (simulateQ (labelledFull env.source (QueryImpl.ofLift unifSpec ProbComp) selected response)
      (accepted env kdf baseImpl kem attachedVerify primitives program post secret selected prepared ready)).run cache =
      (do
        let result ← (PqxdhInitialPrivateKdf.build env.source env.recordWriter kdf
          (PqxdhInitialReplyErasure.kernelOf false response) env.aux env.senderId env.index env.metadata
          (PqxdhInitialBuilderCut.eraseRoot ready)).run prepared.1.context.selection.2
        (simulateQ (labelledFull env.source (QueryImpl.ofLift unifSpec ProbComp) selected response)
          (Prod.fst <$> (simulateQ (PqxdhInitialPrivateBeacon.target attachedVerify primitives 1 env.source kdf env.localImpl
            env.recordWriter env.senderId env.route env.decode baseImpl kem secret ready.ciphertext)
            (post prepared.1.context.selection.1 result.1)).run (result.2, prepared.2))).run cache) := by
  simp only [accepted, simulateQ_bind, StateT.run_bind, PqxdhInitialPrivateBuilder.build_response, bind_map_left]

noncomputable def random {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1)) : ProbComp Bool := do
  let (context, _) ← PqxdhInitialLegalObserver.sample env baseImpl kem attachedVerify primitives program post
  let output ← $ᵗ HmacBlock
  observe env kdf baseImpl kem attachedVerify primitives program post context (RawCtxSelectedInitialConstructor.response64 output)

/-- The source-derived random64 initializer endpoint is exactly this pre-first-record execution with the real private handler; it does not begin from an arbitrary already-established family. -/
theorem random_source {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1)) :
    random env (RawCtxSourceHkdf.kdfImpl env.source) baseImpl kem attachedVerify primitives program post =
      PqxdhInitialCurrentSecrecy.random env baseImpl kem attachedVerify primitives program post := by
  simp only [random, PqxdhInitialCurrentSecrecy.random, observe_source]

end BeaconcryptCore.Computational.PqxdhInitialPrivateCurrent

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPrivateCurrent.accepted_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPrivateCurrent.accepted_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPrivateCurrent.observe_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPrivateCurrent.observe_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPrivateCurrent.accepted_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPrivateCurrent.accepted_response

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPrivateCurrent.random_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPrivateCurrent.random_source
