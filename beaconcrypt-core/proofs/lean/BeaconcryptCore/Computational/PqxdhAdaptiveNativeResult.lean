import BeaconcryptCore.Computational.PqxdhAdaptiveGeneratedResult
import BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingSecrecy

/-!
One actual source execution retains the final target choice across generation, verification, every common candidate and the accepted registration path. Target projection is proved against the existing authenticated evolving-chain experiment. No honest-target selection or per-target simulation equality is assumed.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhAdaptiveNativeResult
open PqxdhAdaptiveTargetPost PqxdhAdaptiveAcceptedResult PqxdhAdaptiveCommonResult
open PqxdhAdaptiveGeneratedResult PqxdhInitializerSecrecy
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhHiddenRoot PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhPhase1AcceptanceOracle PqxdhPhase2GeneratedDriver
open PqxdhSourceAuthenticatedRoot PqxdhPrivateRootSource
open PqxdhPrivateAcceptedRoot (Ready ready)
variable {ι Choice M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAdaptiveTargetPost.Post Choice program.Selection baseSpec S (B + 1))
    (targets : Choice → Target S (B + 1))

noncomputable def nativeAccepted
    (secret : KemSK) (prepared : Prepared setup (driver env.toDriverEnvironment program).State) (ready : Ready) : ProbComp (Decision Choice) :=
  simulateQ (PqxdhPhase2PostScheduler.interpretation env.source baseImpl kem secret ready.ciphertext)
    (PqxdhAdaptiveAcceptedResult.target env attachedVerify primitives program post prepared ready targets)

/-- The private native interpreter preserves the adaptive choice while retaining the selected KEM secret internally. -/
theorem nativeAccepted_map [DecidableEq Choice] (selected : Choice)
    (secret : KemSK) (prepared : Prepared setup (driver env.toDriverEnvironment program).State) (ready : Ready) :
    PqxdhInitialRootEventExperiment.nativeAccepted env baseImpl kem attachedVerify primitives program (mapPost post (choose selected))
      (PqxdhInitialRootEventSecrecy.accepted env attachedVerify primitives program (mapPost post (choose selected))
        (targets selected).owner (targets selected).number (targets selected).ancestors (targets selected).disclosed)
      secret prepared ready =
    choose selected <$> nativeAccepted env baseImpl kem attachedVerify primitives program post targets secret prepared ready := by
  simp only [PqxdhInitialRootEventExperiment.nativeAccepted, PqxdhInitialRootEventSecrecy.accepted,
    PqxdhAdaptiveAcceptedResult.target_map, nativeAccepted, simulateQ_map]

noncomputable def nativeAfterEncapsulation
    (secret : KemSK) (prepared : Prepared setup (driver env.toDriverEnvironment program).State)
    (ephemeral : List.Vector UInt8 32) (encapsulated : Option (MlKem768Ciphertext × MlKemSharedSecret)) : ProbComp (Decision Choice) :=
  match encapsulated with
  | none => evalKem baseImpl kem secret (PqxdhAdaptiveCommonResult.observe env.source none attachedVerify primitives 1 setup (common env program post)
      (some prepared.1) ⟨some ephemeral, none, .error .badEncoding, env.server⟩ prepared.2)
  | some (ciphertext, shared) =>
      match rootFailure env.source.crypto env.server.ikSk ephemeral.toList prepared.1.context.publicIdentity.ed25519
        prepared.1.context.generated.before.publicKey prepared.1.context.generated.after.publicKey with
      | some failure => evalKem baseImpl kem secret (PqxdhAdaptiveCommonResult.observe env.source none attachedVerify primitives 1 setup (common env program post)
          (some prepared.1) ⟨some ephemeral, some ciphertext, .error failure, env.server⟩ prepared.2)
      | none => nativeAccepted env baseImpl kem attachedVerify primitives program post targets secret prepared
          (ready env.server env.application prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.after.publicKey
            ephemeral ciphertext (productionHiddenRoot env.source
              (serverCoordinates env.source.crypto env.server.ikSk ephemeral.toList prepared.1.context.publicIdentity.ed25519
                prepared.1.context.generated.before.publicKey prepared.1.context.generated.after.publicKey) shared))

/-- Optional encapsulation and conversion/DH rejection keep the original common path and final adaptive choice. -/
theorem nativeAfterEncapsulation_map [DecidableEq Choice] (selected : Choice)
    (secret : KemSK) (prepared : Prepared setup (driver env.toDriverEnvironment program).State)
    (ephemeral : List.Vector UInt8 32) (encapsulated : Option (MlKem768Ciphertext × MlKemSharedSecret)) :
    PqxdhInitialRootEventExperiment.nativeAfterEncapsulation env baseImpl kem attachedVerify primitives program (mapPost post (choose selected))
      (PqxdhInitialRootEventSecrecy.accepted env attachedVerify primitives program (mapPost post (choose selected))
        (targets selected).owner (targets selected).number (targets selected).ancestors (targets selected).disclosed)
      secret prepared ephemeral encapsulated =
    choose selected <$> nativeAfterEncapsulation env baseImpl kem attachedVerify primitives program post targets secret prepared ephemeral encapsulated := by
  cases encapsulated with
  | none =>
    simp only [PqxdhInitialRootEventExperiment.nativeAfterEncapsulation, nativeAfterEncapsulation,
      ← common_map env program post selected, PqxdhAdaptiveCommonResult.observe_map, evalKem, simulateQ_map]
  | some pair =>
    rcases pair with ⟨ciphertext, shared⟩
    cases failure : rootFailure env.source.crypto env.server.ikSk ephemeral.toList prepared.1.context.publicIdentity.ed25519
      prepared.1.context.generated.before.publicKey prepared.1.context.generated.after.publicKey <;>
      simp only [PqxdhInitialRootEventExperiment.nativeAfterEncapsulation, nativeAfterEncapsulation, failure,
        nativeAccepted_map, ← common_map env program post selected, PqxdhAdaptiveCommonResult.observe_map,
        evalKem, simulateQ_map]

noncomputable def nativeNext
    (secret : KemSK) (prepared : Prepared setup (driver env.toDriverEnvironment program).State) : ProbComp (Decision Choice) :=
  if targetEligible env.parameters prepared then do
    let ephemeral ← simulateQ (kemAmbientImpl baseImpl) env.ephemeralGen
    let encapsulated ← simulateQ (kemAmbientImpl baseImpl) (env.native.encaps prepared.1.context.generated.target)
    nativeAfterEncapsulation env baseImpl kem attachedVerify primitives program post targets secret prepared ephemeral encapsulated
  else evalKem baseImpl kem secret (PqxdhAdaptiveCommonResult.allCandidateCommon env.source kem env.native attachedVerify primitives 1 setup
    (common env program post) (some prepared.1) prepared.2 env.server env.application env.ephemeralGen)

/-- Internally selected eligibility keeps honest unchanged, changed, attacker-owned and rejected candidates in the same source experiment. -/
theorem nativeNext_map [DecidableEq Choice] (selected : Choice)
    (secret : KemSK) (prepared : Prepared setup (driver env.toDriverEnvironment program).State) :
    PqxdhInitialRootEventExperiment.nativeNext env baseImpl kem attachedVerify primitives program (mapPost post (choose selected))
      (PqxdhInitialRootEventSecrecy.accepted env attachedVerify primitives program (mapPost post (choose selected))
        (targets selected).owner (targets selected).number (targets selected).ancestors (targets selected).disclosed) secret prepared =
    choose selected <$> nativeNext env baseImpl kem attachedVerify primitives program post targets secret prepared := by
  simp only [PqxdhInitialRootEventExperiment.nativeNext, nativeNext]
  split
  · simp only [nativeAfterEncapsulation_map, map_bind]
  · simp only [← common_map env program post selected, PqxdhAdaptiveCommonResult.allCandidateCommon_map, evalKem, simulateQ_map]

/-- One source-ordered generated run returns the adversary's adaptive target and the exact selected source event. -/
noncomputable def actual : ProbComp (Decision Choice) :=
  PqxdhGeneratedNativeContinuation.nativeContinued attachedVerify primitives baseImpl kem setup (driver env.toDriverEnvironment program)
    (nativeNext env baseImpl kem attachedVerify primitives program post targets) rejected

/-- Every maintained fixed-target source experiment is an exact result projection of one common original execution. The selector and all private generators run only once in their production order. -/
theorem actual_map [DecidableEq Choice] (selected : Choice) :
    PqxdhInitialRootEventSecrecy.actual env baseImpl kem attachedVerify primitives program (mapPost post (choose selected))
      (targets selected).owner (targets selected).number (targets selected).ancestors (targets selected).disclosed =
    choose selected <$> actual env baseImpl kem attachedVerify primitives program post targets := by
  simp only [PqxdhInitialRootEventSecrecy.actual, PqxdhInitialRootEventExperiment.actual,
    actual, PqxdhGeneratedNativeContinuation.nativeContinued, map_bind]
  apply bind_congr
  intro stopped
  cases stopped.1 with
  | none => simp [rejected, choose]
  | some output => exact nativeNext_map env baseImpl kem attachedVerify primitives program post targets selected _ _

end BeaconcryptCore.Computational.PqxdhAdaptiveNativeResult

/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveNativeResult.nativeAccepted_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveNativeResult.nativeAccepted_map
/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveNativeResult.nativeAfterEncapsulation_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveNativeResult.nativeAfterEncapsulation_map
/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveNativeResult.nativeNext_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveNativeResult.nativeNext_map
/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveNativeResult.actual_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveNativeResult.actual_map
