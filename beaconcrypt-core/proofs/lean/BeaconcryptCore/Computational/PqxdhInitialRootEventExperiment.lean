import BeaconcryptCore.Computational.PqxdhInitialRootEventAccepted

/-! The generated all-candidate source prefix admits an arbitrary executable accepted continuation. This extension keeps authentication filtering and KEM target selection before that continuation. The concrete consuming callback is the complete instrumented source event, never an assumed final game equality. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialRootEventExperiment
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhPhase2GeneratedDriver PqxdhGeneratedBeaconState
open PqxdhPrivateRootSource PqxdhPrivateAcceptedRoot PqxdhKemIndCca PqxdhInitializerSecrecy
open PqxdhSourceAuthenticatedRoot
open PqxdhHiddenRoot PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhChallengeSecretRouting
variable {ι : Type} {baseSpec : OracleSpec ι} {M P I K X Response A KemSK : Type} {S B : Nat}

open PqxdhAuthenticatedRootExperiment

/-- The native interpreter alone supplies the selected secret to actual root/CCA execution of the complete source-event continuation. -/
noncomputable def nativeAccepted {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (_attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (_primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (_post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (accepted : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State → Ready → OracleComp (LocalPostSpec baseSpec) Bool)
    (secret : KemSK) (prepared : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State) (ready : Ready) : ProbComp Bool :=
  simulateQ (PqxdhPhase2PostScheduler.interpretation env.source baseImpl kem secret ready.ciphertext) (accepted prepared ready)

/-- The actual target path keeps optional encapsulation before validation and every failure on the unblocked public path. -/
noncomputable def nativeAfterEncapsulation {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (accepted : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State → Ready → OracleComp (LocalPostSpec baseSpec) Bool)
    (secret : KemSK) (prepared : Prepared setup (driver env.toDriverEnvironment program).State)
    (ephemeral : List.Vector UInt8 32) (encapsulated : Option (MlKem768Ciphertext × MlKemSharedSecret)) : ProbComp Bool :=
  match encapsulated with
  | none => evalKem baseImpl kem secret (observe env.source none attachedVerify primitives 1 setup (commonObserver env program post)
      (some prepared.1) ⟨some ephemeral, none, .error .badEncoding, env.server⟩ prepared.2)
  | some (ciphertext, shared) =>
      match rootFailure env.source.crypto env.server.ikSk ephemeral.toList prepared.1.context.publicIdentity.ed25519
        prepared.1.context.generated.before.publicKey prepared.1.context.generated.after.publicKey with
      | some failure => evalKem baseImpl kem secret (observe env.source none attachedVerify primitives 1 setup (commonObserver env program post)
          (some prepared.1) ⟨some ephemeral, some ciphertext, .error failure, env.server⟩ prepared.2)
      | none => nativeAccepted env baseImpl kem attachedVerify primitives program post accepted secret prepared
          (ready env.server env.application prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.after.publicKey
            ephemeral ciphertext (productionHiddenRoot env.source
              (serverCoordinates env.source.crypto env.server.ikSk ephemeral.toList prepared.1.context.publicIdentity.ed25519
                prepared.1.context.generated.before.publicKey prepared.1.context.generated.after.publicKey) shared))

/-- All candidates occur in the same actual source run; eligibility is decided internally from the accepted fields and retained reveal/consumption state. -/
noncomputable def nativeNext {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (accepted : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State → Ready → OracleComp (LocalPostSpec baseSpec) Bool)
    (secret : KemSK) (prepared : Prepared setup (driver env.toDriverEnvironment program).State) : ProbComp Bool :=
  if targetEligible env.parameters prepared then do
    let ephemeral ← simulateQ (kemAmbientImpl baseImpl) env.ephemeralGen
    let encapsulated ← simulateQ (kemAmbientImpl baseImpl) (env.native.encaps prepared.1.context.generated.target)
    nativeAfterEncapsulation env baseImpl kem attachedVerify primitives program post accepted secret prepared ephemeral encapsulated
  else evalKem baseImpl kem secret (allCandidateCommon env.source kem env.native attachedVerify primitives 1 setup
    (commonObserver env program post) (some prepared.1) prepared.2 env.server env.application env.ephemeralGen)

/-- The actual experiment generates identity, prekey, KEM and one-time material in source order before its complete native continuation. -/
noncomputable def actual {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (accepted : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State → Ready → OracleComp (LocalPostSpec baseSpec) Bool) : ProbComp Bool :=
  PqxdhGeneratedNativeContinuation.nativeContinued attachedVerify primitives baseImpl kem setup (driver env.toDriverEnvironment program)
    (nativeNext env baseImpl kem attachedVerify primitives program post accepted) false

/-- The same private source continuation with ordinary total encapsulation only on the internally eligible generated key. -/
noncomputable def totalNext {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (accepted : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State → Ready → OracleComp (LocalPostSpec baseSpec) Bool)
    (secret : KemSK) (prepared : Prepared setup (driver env.toDriverEnvironment program).State) : ProbComp Bool :=
  if targetEligible env.parameters prepared then do
    let ephemeral ← simulateQ (kemAmbientImpl baseImpl) env.ephemeralGen
    let encapsulated ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps prepared.1.context.generated.target)
    nativeAfterEncapsulation env baseImpl kem attachedVerify primitives program post accepted secret prepared ephemeral (some encapsulated)
  else evalKem baseImpl kem secret (allCandidateCommon env.source kem env.native attachedVerify primitives 1 setup
    (commonObserver env program post) (some prepared.1) prepared.2 env.server env.application env.ephemeralGen)

/-- Filtering the single changed-acceptance event is the only authentication game change. -/
noncomputable def filteredNext {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (accepted : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State → Ready → OracleComp (LocalPostSpec baseSpec) Bool)
    (secret : KemSK) (prepared : Prepared setup (driver env.toDriverEnvironment program).State) : ProbComp Bool :=
  if PqxdhPrivatePhase1Prefix.changedBit (some prepared.1, prepared.2) then pure false
  else totalNext env baseImpl kem attachedVerify primitives program post accepted secret prepared

/-- The complete actual continuation retains the encapsulated secret only inside its private interpreter. -/
noncomputable def nativeAfter {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (accepted : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State → Ready → OracleComp (LocalPostSpec baseSpec) Bool)
    (_key : PqxdhKemIndCca.MlKem768PublicKey) (secret : KemSK) (mode : Mode setup (driver env.toDriverEnvironment program).State)
    (ciphertext : MlKem768Ciphertext) (shared : MlKemSharedSecret) : ProbComp Bool :=
  match mode with
  | .completed decision => pure decision
  | .pending prepared ephemeral => nativeAccepted env baseImpl kem attachedVerify primitives program post accepted secret prepared
      (ready env.server env.application prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.after.publicKey
        ephemeral ciphertext (productionHiddenRoot env.source
          (serverCoordinates env.source.crypto env.server.ikSk ephemeral.toList prepared.1.context.publicIdentity.ed25519
            prepared.1.context.generated.before.publicKey prepared.1.context.generated.after.publicKey) shared))


/-- Only the accepted resume callback changes; the full original preparation, common candidates and target coordinates are retained. -/
noncomputable def protocol {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (accepted : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State → Ready → OracleComp (LocalPostSpec baseSpec) Bool) : Protocol baseSpec :=
  { PqxdhAuthenticatedRootExperiment.protocol env kem attachedVerify primitives program post with
    resume := fun _ ciphertext mode root => match mode with
      | .completed decision => pure decision
      | .pending prepared ephemeral => match root with
        | none => pure false
        | some value => accepted prepared
            (ready env.server env.application prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.after.publicKey
              ephemeral ciphertext value) }

/-- All later private roots use the same encapsulated secret on a good decapsulation sample, for the complete executable callback. -/
theorem nativeAccepted_reduction {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (accepted : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State → Ready → OracleComp (LocalPostSpec baseSpec) Bool)
    (secret : KemSK) (prepared : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State) (ready : Ready)
    (shared : MlKemSharedSecret) (agreement : kem.decaps secret ready.ciphertext = pure (some shared)) :
    nativeAccepted env baseImpl kem attachedVerify primitives program post accepted secret prepared ready =
      simulateQ (kemAmbientImpl baseImpl) (simulateQ (publicImpl kem secret ready.ciphertext)
        (simulateQ (PqxdhChallengeSecretRouting.route env.source ready.ciphertext shared) (accepted prepared ready))) := by
  simp only [nativeAccepted, PqxdhPhase2PostScheduler.interpretation, QueryImpl.simulateQ_compose,
    PqxdhChallengeSecretRouting.route_complete env.source kem secret ready.ciphertext shared agreement]

end BeaconcryptCore.Computational.PqxdhInitialRootEventExperiment

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventExperiment.nativeAccepted_reduction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventExperiment.nativeAccepted_reduction
