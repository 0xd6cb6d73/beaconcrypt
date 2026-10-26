import BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriverBounds
import BeaconcryptCore.Computational.PqxdhPhase2GeneratedServerFields
import BeaconcryptCore.Computational.PqxdhGeneratedNativeContinuation
import BeaconcryptCore.Computational.PqxdhPhase2PostScheduler
import BeaconcryptCore.Computational.PqxdhProtocolNativeAcceptance

/-!
One source-shaped authenticated root experiment retains the generated Phase1 prefix and the complete adaptive native scheduler on both sides of Server registration. Only the eligible unchanged target uses the blocked public postchallenge interface and opaque private root routing. Arbitrary accepted keys and every rejection keep the original unblocked scheduler. The native selected secret is a private interpreter argument; it is absent from the executable protocol's state, prepare and resume interfaces.
-/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhAuthenticatedRootExperiment
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhPhase2GeneratedDriver PqxdhGeneratedBeaconState
open PqxdhPrivateRootSource PqxdhPrivateAcceptedRoot PqxdhKemIndCca PqxdhInitializerSecrecy
open PqxdhSourceAuthenticatedRoot
open PqxdhHiddenRoot PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhChallengeSecretRouting
variable {ι : Type} {baseSpec : OracleSpec ι} {M P I K X Response A KemSK : Type} {S B : Nat}

structure Environment (setup : StatefulPhase1Setup baseSpec) (M P I K X Response A : Type) (S B : Nat)
    extends toDriverEnvironment : PqxdhPhase2GeneratedDriver.Environment setup M P I K X Response A S B where
  native : PqxdhOptionalKemSource.SourceKemInterface baseSpec
  server : Pqxdh.ServerState
  application : Option Pqxdh.Bytes
  ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32)
  aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec
    (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)
  index : Fin S
  metadata : P

def Environment.parameters {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K X Response A S B) : Parameters baseSpec :=
  ⟨env.source, env.native, env.server, env.application, env.ephemeralGen⟩

abbrev Post (Selection : Type) (S B : Nat) := Selection →
  RustM (Option PqxdhServerRegistrationPublication.Response) →
    OracleComp (PqxdhPhase2SourceScheduler.Spec baseSpec S B) Bool

/-- This public lifting exposes no private root requests and leaves every source/CCA request intact. -/
def selectorLift : QueryImpl (SelectorSpec baseSpec) (OracleComp (CorrelatedSpec baseSpec))
  | .inl request => (CorrelatedSpec baseSpec).query (.inl (.inl request))
  | .inr request => (CorrelatedSpec baseSpec).query (.inl (.inr (.inl request)))

/-- Common candidates and all failures use the original compiler, with no challenge marker or block. -/
noncomputable def commonObserver {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K X Response A S B)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1)) :
    Continuation setup (driver env.toDriverEnvironment program).State where
  completed output _ := match output with
    | none => pure false
    | some output => simulateQ selectorLift (Prod.fst <$>
        (simulateQ (PqxdhPhase2SourceScheduler.compiler env.source env.recordWriter env.senderId env.route env.decode env.localImpl)
          (post output.context.selection.1 (ok none))).run output.context.selection.2)
  accepted output ready := match output with
    | none => pure false
    | some output => do
        let result ← PqxdhProtocolRegistration.coins
          ((PqxdhRegistrationProtocolState.build env.source env.recordWriter env.aux env.senderId
            env.index env.metadata ready).run output.context.selection.2)
        simulateQ selectorLift (Prod.fst <$>
          (simulateQ (PqxdhPhase2SourceScheduler.compiler env.source env.recordWriter env.senderId env.route env.decode env.localImpl)
            (post output.context.selection.1 result.1)).run result.2)

/-- The original builder precedes the complete actual native postchallenge schedule. -/
noncomputable def nativeAccepted {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (secret : KemSK) (prepared : Prepared setup (driver env.toDriverEnvironment program).State) (ready : Ready) : ProbComp Bool := do
  let result ← (PqxdhRegistrationProtocolState.build env.source env.recordWriter env.aux env.senderId
    env.index env.metadata ready).run prepared.1.context.selection.2
  Prod.fst <$> (simulateQ (PqxdhPhase2PostScheduler.actual attachedVerify primitives 1 env.source env.localImpl
    env.recordWriter env.senderId env.route env.decode baseImpl kem secret ready.ciphertext)
    (post prepared.1.context.selection.1 result.1)).run (result.2, prepared.2)

/-- The target compiler receives only the original ready root and public ciphertext; all complete private source fields remain retained. -/
noncomputable def targetAccepted {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K X Response A S B)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (prepared : Prepared setup (driver env.toDriverEnvironment program).State) (ready : Ready) :
    OracleComp (LocalPostSpec baseSpec) Bool := do
  let result ← localCoins ((PqxdhRegistrationProtocolState.build env.source env.recordWriter env.aux env.senderId
    env.index env.metadata ready).run prepared.1.context.selection.2)
  Prod.fst <$> (simulateQ (PqxdhPhase2PostScheduler.target attachedVerify primitives 1 env.source env.localImpl
    env.recordWriter env.senderId env.route env.decode ready.ciphertext)
    (post prepared.1.context.selection.1 result.1)).run (result.2, prepared.2)

/-- The actual target path keeps optional encapsulation before validation and every failure on the unblocked public path. -/
noncomputable def nativeAfterEncapsulation {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
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
      | none => nativeAccepted env baseImpl kem attachedVerify primitives program post secret prepared
          (ready env.server env.application prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.after.publicKey
            ephemeral ciphertext (productionHiddenRoot env.source
              (serverCoordinates env.source.crypto env.server.ikSk ephemeral.toList prepared.1.context.publicIdentity.ed25519
                prepared.1.context.generated.before.publicKey prepared.1.context.generated.after.publicKey) shared))

/-- All candidates occur in the same actual source run; eligibility is decided internally from the accepted fields and retained reveal/consumption state. -/
noncomputable def nativeNext {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (secret : KemSK) (prepared : Prepared setup (driver env.toDriverEnvironment program).State) : ProbComp Bool :=
  if targetEligible env.parameters prepared then do
    let ephemeral ← simulateQ (kemAmbientImpl baseImpl) env.ephemeralGen
    let encapsulated ← simulateQ (kemAmbientImpl baseImpl) (env.native.encaps prepared.1.context.generated.target)
    nativeAfterEncapsulation env baseImpl kem attachedVerify primitives program post secret prepared ephemeral encapsulated
  else evalKem baseImpl kem secret (allCandidateCommon env.source kem env.native attachedVerify primitives 1 setup
    (commonObserver env program post) (some prepared.1) prepared.2 env.server env.application env.ephemeralGen)

/-- The ordinary CCA protocol preserves the source prefix and explicit common/pending branch. Its state contains no generated KEM secret. -/
noncomputable def protocol {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K X Response A S B)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1)) : Protocol baseSpec where
  State := Mode setup (driver env.toDriverEnvironment program).State
  prepare key := PqxdhGeneratedRootSource.borrowedPrefix attachedVerify primitives setup (driver env.toDriverEnvironment program) key >>=
    dispatch kem env.parameters attachedVerify primitives setup (commonObserver env program post)
  initialCoordinates _ _ mode := match mode with
    | .completed _ => none
    | .pending prepared ephemeral => some (serverCoordinates env.source.crypto env.server.ikSk ephemeral.toList
        prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.before.publicKey prepared.1.context.generated.after.publicKey)
  resume _ ciphertext mode root := match mode with
    | .completed decision => pure decision
    | .pending prepared ephemeral => match root with
      | none => pure false
      | some value => targetAccepted env attachedVerify primitives program post prepared
          (ready env.server env.application prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.after.publicKey
            ephemeral ciphertext value)

/-- The actual experiment generates identity, prekey, KEM and one-time material in source order before its complete native continuation. -/
noncomputable def actual {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1)) : ProbComp Bool :=
  PqxdhGeneratedNativeContinuation.nativeContinued attachedVerify primitives baseImpl kem setup (driver env.toDriverEnvironment program)
    (nativeNext env baseImpl kem attachedVerify primitives program post) false

/-- The same private source continuation with ordinary total encapsulation only on the internally eligible generated key. -/
noncomputable def totalNext {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (secret : KemSK) (prepared : Prepared setup (driver env.toDriverEnvironment program).State) : ProbComp Bool :=
  if targetEligible env.parameters prepared then do
    let ephemeral ← simulateQ (kemAmbientImpl baseImpl) env.ephemeralGen
    let encapsulated ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps prepared.1.context.generated.target)
    nativeAfterEncapsulation env baseImpl kem attachedVerify primitives program post secret prepared ephemeral (some encapsulated)
  else evalKem baseImpl kem secret (allCandidateCommon env.source kem env.native attachedVerify primitives 1 setup
    (commonObserver env program post) (some prepared.1) prepared.2 env.server env.application env.ephemeralGen)

/-- Filtering the single changed-acceptance event is the only authentication game change. -/
noncomputable def filteredNext {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (secret : KemSK) (prepared : Prepared setup (driver env.toDriverEnvironment program).State) : ProbComp Bool :=
  if PqxdhPrivatePhase1Prefix.changedBit (some prepared.1, prepared.2) then pure false
  else totalNext env baseImpl kem attachedVerify primitives program post secret prepared

/-- The complete actual continuation retains the encapsulated secret only inside its private interpreter. -/
noncomputable def nativeAfter {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (_key : PqxdhKemIndCca.MlKem768PublicKey) (secret : KemSK) (mode : Mode setup (driver env.toDriverEnvironment program).State)
    (ciphertext : MlKem768Ciphertext) (shared : MlKemSharedSecret) : ProbComp Bool :=
  match mode with
  | .completed decision => pure decision
  | .pending prepared ephemeral => nativeAccepted env baseImpl kem attachedVerify primitives program post secret prepared
      (ready env.server env.application prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.after.publicKey
        ephemeral ciphertext (productionHiddenRoot env.source
          (serverCoordinates env.source.crypto env.server.ikSk ephemeral.toList prepared.1.context.publicIdentity.ed25519
            prepared.1.context.generated.before.publicKey prepared.1.context.generated.after.publicKey) shared))

/-- Explicitly lifted local builder coins retain their original evaluated distribution. -/
theorem localCoins_actual {Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (challenge : MlKem768Ciphertext) (work : ProbComp Result) :
    simulateQ (PqxdhPhase2PostScheduler.interpretation source baseImpl kem secret challenge) (localCoins work) = work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [localCoins, simulateQ_bind, simulateQ_spec_query]
    change ((unifSpec.query query : ProbComp _) >>= fun reply =>
      simulateQ (PqxdhPhase2PostScheduler.interpretation source baseImpl kem secret challenge) (localCoins (next reply))) = _
    simp only [ih]

variable {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))

/-- The exact builder and complete adaptive schedule consume the same ready root on a good KEM sample. -/
theorem nativeAccepted_actual
    (secret : KemSK) (prepared : Prepared setup (driver env.toDriverEnvironment program).State) (ready : Ready)
    (shared : MlKemSharedSecret) (agreement : kem.decaps secret ready.ciphertext = pure (some shared)) :
    nativeAccepted env baseImpl kem attachedVerify primitives program post secret prepared ready =
      simulateQ (PqxdhPhase2PostScheduler.interpretation env.source baseImpl kem secret ready.ciphertext)
        (targetAccepted env attachedVerify primitives program post prepared ready) := by
  simp only [nativeAccepted, targetAccepted, simulateQ_bind, localCoins_actual, simulateQ_map]
  apply bind_congr
  intro result
  exact congrArg (Functor.map Prod.fst)
    (PqxdhPhase2PostScheduler.schedule_actual attachedVerify primitives 1 env.source env.localImpl env.recordWriter
      env.senderId env.route env.decode baseImpl kem secret ready.ciphertext shared agreement
      (post prepared.1.context.selection.1 result.1) (result.2, prepared.2))

/-- All matching private roots use the same encapsulated secret throughout the original accepted continuation. -/
theorem nativeAccepted_reduction
    (secret : KemSK) (prepared : Prepared setup (driver env.toDriverEnvironment program).State) (ready : Ready)
    (shared : MlKemSharedSecret) (agreement : kem.decaps secret ready.ciphertext = pure (some shared)) :
    nativeAccepted env baseImpl kem attachedVerify primitives program post secret prepared ready =
      simulateQ (kemAmbientImpl baseImpl) (simulateQ (publicImpl kem secret ready.ciphertext)
        (simulateQ (PqxdhChallengeSecretRouting.route env.source ready.ciphertext shared)
          (targetAccepted env attachedVerify primitives program post prepared ready))) := by
  rw [nativeAccepted_actual env baseImpl kem attachedVerify primitives program post secret prepared ready shared agreement,
    route_complete env.source kem secret ready.ciphertext shared agreement]
  exact QueryImpl.simulateQ_compose _ _ _

end BeaconcryptCore.Computational.PqxdhAuthenticatedRootExperiment

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootExperiment.localCoins_actual' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootExperiment.localCoins_actual

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootExperiment.nativeAccepted_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootExperiment.nativeAccepted_actual

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootExperiment.nativeAccepted_reduction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootExperiment.nativeAccepted_reduction
