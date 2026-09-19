import BeaconcryptCore.Computational.PqxdhInitialServiceBuilder
import BeaconcryptCore.Computational.PqxdhInitialServicePost
import BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid

/-!
The current authenticated-root continuation is extended by one common private initializer response interface. The original Server builder and every later attempted Beacon finish use that interface at their actual source positions. Interpreting its responses by fixed HKDF recovers the complete current target experiment, including all pending/completed modes and optional root outcomes. Public HKDF remains the original real service.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialServiceExperiment
open PqxdhInitialResponseService PqxdhAuthenticatedRootExperiment PqxdhPhase2GeneratedDriver
open PqxdhPrivateAcceptedRoot PqxdhStatefulPhase1EufCma PqxdhEd25519EufCma PqxdhJointIdentity
open PqxdhSourceAuthenticatedRoot PqxdhChallengeSecretRouting PqxdhKemIndCca PqxdhJointKdfGame
open PqxdhHiddenRoot PqxdhSecretInputKdf PqxdhPrivateRootSource
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}

abbrev RunSpec (baseSpec : OracleSpec ι) := PqxdhInitialServicePost.RunSpec baseSpec

def builderLift : QueryImpl PqxdhInitialServiceBuilder.RunSpec (OracleComp (RunSpec baseSpec))
  | .inl coin => (RunSpec baseSpec).query (.inl (.inl (.inl (.inl coin))))
  | .inr request => initial request

/-- The builder's original coins retain their original public coin channel, and its new initializer requests are the very same common private callbacks. -/
theorem builder_source {Result : Type} (fixed : FixedHkdfSha512NoSaltSource)
    (work : OracleComp PqxdhInitialServiceBuilder.RunSpec Result) :
    simulateQ (source fixed) (simulateQ (builderLift (baseSpec := baseSpec)) work) =
      localCoins (simulateQ (source fixed) work) := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      cases query <;> simp [builderLift, initial, source, localCoins, OracleSpec.query, ih]

noncomputable def accepted {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (prepared : Prepared setup (driver env.toDriverEnvironment program).State) (ready : Ready) :
    OracleComp (RunSpec baseSpec) Bool := do
  let result ← simulateQ builderLift
    ((PqxdhInitialServiceBuilder.protocolBuild env.source env.recordWriter env.aux env.senderId
      env.index env.metadata ready).run prepared.1.context.selection.2)
  Prod.fst <$> (simulateQ (PqxdhInitialServicePost.target attachedVerify primitives 1 env.source env.localImpl
    env.recordWriter env.senderId env.route env.decode ready.ciphertext)
    (post prepared.1.context.selection.1 result.1)).run (result.2, prepared.2)

/-- The complete current authenticated accepted-root continuation is recovered, with the original Server build before the adaptive Beacon/source schedule and all complete private state retained. -/
theorem accepted_source {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (prepared : Prepared setup (driver env.toDriverEnvironment program).State) (ready : Ready) :
    simulateQ (source env.source) (accepted env attachedVerify primitives program post prepared ready) =
      targetAccepted env attachedVerify primitives program post prepared ready := by
  simp only [accepted, targetAccepted, simulateQ_bind, builder_source,
    PqxdhInitialServiceBuilder.protocol_source, simulateQ_map, PqxdhInitialServicePost.target_program]

noncomputable def resume {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (ciphertext : MlKem768Ciphertext) (mode : Mode setup (driver env.toDriverEnvironment program).State)
    (root : Option RootOutput) : OracleComp (RunSpec baseSpec) Bool := match mode with
  | .completed decision => pure decision
  | .pending prepared ephemeral => match root with
    | none => pure false
    | some value => accepted env attachedVerify primitives program post prepared
        (ready env.server env.application prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.after.publicKey
          ephemeral ciphertext value)

/-- Every original completed/pending mode and optional root branch is preserved; no honest-target or successful-initializer premise is required. -/
theorem resume_source {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (key : PqxdhKemIndCca.MlKem768PublicKey) (ciphertext : MlKem768Ciphertext)
    (mode : Mode setup (driver env.toDriverEnvironment program).State) (root : Option RootOutput) :
    simulateQ (source env.source) (resume env attachedVerify primitives program post ciphertext mode root) =
      (protocol env kem attachedVerify primitives program post).resume key ciphertext mode root := by
  cases mode with
  | completed decision => rfl
  | pending prepared ephemeral => cases root with
    | none => rfl
    | some value => exact accepted_source env attachedVerify primitives program post prepared _

abbrev RootRunSpec := PqxdhInitialResponseService.Spec PqxdhCorrelatedExpand.RootSpec

noncomputable def rootPost (fixed : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK) (challenge : MlKem768Ciphertext) :
    QueryImpl (RunSpec baseSpec) (OracleComp RootRunSpec)
  | .inl query => simulateQ original (PqxdhCorrelatedExpand.rootPost fixed baseImpl kem secret challenge query)
  | .inr request => initial request

/-- The root interpreter retains both ordinary CCA/public behavior and every matching-ciphertext root query, while the added initializer service is interpreted by the same real source on either side. -/
theorem rootPost_source (fixed : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK) (challenge : MlKem768Ciphertext) :
    source fixed ∘ₛ rootPost fixed baseImpl kem secret challenge =
      PqxdhCorrelatedExpand.rootPost fixed baseImpl kem secret challenge ∘ₛ source fixed := by
  funext query
  cases query with
  | inl query => simpa [QueryImpl.compose, rootPost, source, OracleSpec.query] using
      (original_program fixed (PqxdhCorrelatedExpand.rootPost fixed baseImpl kem secret challenge query))
  | inr request => simp [QueryImpl.compose, rootPost, initial, source, OracleSpec.query]

noncomputable def rootResume {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (prepared : PqxdhCorrelatedExtractFamily.Prepared (protocol env kem attachedVerify primitives program post) KemSK) :
    OracleComp RootRunSpec Bool := do
  let root ← match (protocol env kem attachedVerify primitives program post).initialCoordinates
      prepared.publicKey prepared.ciphertext prepared.state with
    | none => pure none
    | some known => some <$> RootRunSpec.query (.inl (.inr (PqxdhCorrelatedExtractFamily.coordinates known)))
  simulateQ (rootPost env.source baseImpl kem prepared.secretKey prepared.ciphertext)
    (resume env attachedVerify primitives program post prepared.ciphertext prepared.state root)

/-- The enriched current root continuation retains the exact initial root request and every later correlated root cache request before source interpretation. -/
theorem rootResume_source {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (prepared : PqxdhCorrelatedExtractFamily.Prepared (protocol env kem attachedVerify primitives program post) KemSK) :
    simulateQ (source env.source) (rootResume env baseImpl kem attachedVerify primitives program post prepared) =
      PqxdhCorrelatedExpand.rootResume env.source baseImpl kem (protocol env kem attachedVerify primitives program post) prepared := by
  have continuation (root : Option RootOutput) :
      simulateQ (source env.source)
        (simulateQ (rootPost env.source baseImpl kem prepared.secretKey prepared.ciphertext)
          (resume env attachedVerify primitives program post prepared.ciphertext prepared.state root)) =
      simulateQ (PqxdhCorrelatedExpand.rootPost env.source baseImpl kem prepared.secretKey prepared.ciphertext)
        ((protocol env kem attachedVerify primitives program post).resume prepared.publicKey prepared.ciphertext prepared.state root) := by
    rw [← QueryImpl.simulateQ_compose, rootPost_source, QueryImpl.simulateQ_compose,
      resume_source env kem attachedVerify primitives program post prepared.publicKey]
  simp only [rootResume, PqxdhCorrelatedExpand.rootResume]
  cases (protocol env kem attachedVerify primitives program post).initialCoordinates
    prepared.publicKey prepared.ciphertext prepared.state <;> simp [source, OracleSpec.query, continuation]

noncomputable def reduction {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1)) :
    OracleComp RootRunSpec Bool := do
  let prepared ← simulateQ original (PqxdhCorrelatedExpand.rootCoins
    (PqxdhCorrelatedExtractFamily.prepare baseImpl kem (protocol env kem attachedVerify primitives program post)))
  rootResume env baseImpl kem attachedVerify primitives program post prepared

/-- The exact current authenticated-root reduction is the real initializer interpretation of one enriched source program; the entire preparation runs unchanged before any initial root or initializer response is requested. -/
theorem reduction_source {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1)) :
    simulateQ (source env.source) (reduction env baseImpl kem attachedVerify primitives program post) =
      PqxdhCorrelatedExpand.rootReduction env.source baseImpl kem (protocol env kem attachedVerify primitives program post) := by
  simp only [reduction, PqxdhCorrelatedExpand.rootReduction, simulateQ_bind, original_program, rootResume_source]

end BeaconcryptCore.Computational.PqxdhInitialServiceExperiment

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialServiceExperiment.builder_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialServiceExperiment.builder_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialServiceExperiment.accepted_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialServiceExperiment.accepted_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialServiceExperiment.resume_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialServiceExperiment.resume_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialServiceExperiment.rootPost_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialServiceExperiment.rootPost_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialServiceExperiment.rootResume_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialServiceExperiment.rootResume_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialServiceExperiment.reduction_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialServiceExperiment.reduction_source
