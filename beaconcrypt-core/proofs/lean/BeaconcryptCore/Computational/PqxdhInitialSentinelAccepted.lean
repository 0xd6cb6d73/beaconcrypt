import BeaconcryptCore.Computational.PqxdhInitialSentinelPost
import BeaconcryptCore.Computational.PqxdhInitialPendingAccepted

/-!
The exact accepted authenticated initializer execution removes its analysis marker before the first Server send and through the complete original post schedule. The endpoint begins at the actual prepared source state. Source private HKDF and all public evaluations remain real until their separately stated cryptographic comparisons.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSentinelAccepted
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhInitialBeaconAmbient
open RawCtxSelectedParentTable PqxdhInitialGenericProtocolBuilder PqxdhInitialSentinelSource
variable {M P I D K A : Type} {S B : Nat}

private theorem native_build (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (Base A))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Base A))
    (initial : RustM ConcreteRatchetKernel) (sender : M → Std.U64) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (state : PqxdhRegistrationProtocolState.State M P I D K A S B) :
    (PqxdhInitialPrivateKdf.build source writer kdf initial aux sender index metadata ready).run state =
      Prod.map id (PqxdhInitialGenericProtocol.native ConcreteRatchetKernel.mk) <$>
        (build source (RawCtxGenericNativeCalls.calls (RawCtxMixedShared.sharedImpl source.crypto writer kdf)) aux
          (ConcreteRatchetKernel.refined <$> initial) sender index metadata ready).run
          (PqxdhInitialGenericProtocol.fromNative ConcreteRatchetKernel.refined state) := by
  have law := build_native source writer ConcreteRatchetKernel.mk
    (RawCtxGenericNativeCalls.calls (RawCtxMixedShared.sharedImpl source.crypto writer kdf)) kdf aux
    (RawCtxGenericNativeCalls.send_realized (RawCtxMixedShared.sharedImpl source.crypto writer kdf))
    (ConcreteRatchetKernel.refined <$> initial) sender index metadata ready
    (PqxdhInitialGenericProtocol.fromNative ConcreteRatchetKernel.refined state)
  have round : ConcreteRatchetKernel.mk <$> (ConcreteRatchetKernel.refined <$> initial) = initial := by
    cases initial <;> rfl
  simpa only [round, PqxdhInitialGenericProtocol.roundtrip ConcreteRatchetKernel.refined ConcreteRatchetKernel.mk (fun _ => rfl)] using law

/-- Removing the analysis marker preserves the entire actual Server builder, including first-send failure, erasure, publication and every role and cache field. -/
theorem build_marker (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (other target : RootOutput) (extra : NonceOutput)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Base A))
    (initial : RustM ConcreteRatchetKernel) (sender : M → Std.U64) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) :
    PqxdhInitialPrivateKdf.build (I := I) (D := D) (K := K) (B := B) source writer
      (retainedKdf prior (RawCtxInitialSentinel.entry other extra) target) initial aux sender index metadata ready =
      PqxdhInitialPrivateKdf.build source writer (priorKdf prior) initial aux sender index metadata ready := by
  funext state
  change (PqxdhInitialPrivateKdf.build source writer
    (retainedKdf prior (RawCtxInitialSentinel.entry other extra) target) initial aux sender index metadata ready).run state =
      (PqxdhInitialPrivateKdf.build source writer (priorKdf prior) initial aux sender index metadata ready).run state
  rw [native_build, native_build, PqxdhInitialSentinelRecords.native_calls]

open PqxdhKemIndCca PqxdhCorrelatedExpand PqxdhPhase2SourceAux
open PqxdhPhase1AcceptanceOracle PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPrivateKemSource
open PqxdhCorrelatedExtractFamily PqxdhInitialRootLabelService
open PqxdhAuthenticatedRootExperiment PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhSourceAuthenticatedRoot PqxdhPrivateAcceptedRoot
variable {ι X Response KemSK : Type} {baseSpec : OracleSpec ι}
section Current
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (secret : KemSK) (selected : Message)
    (prepared : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State)
    (ready : Ready) (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (second : Bool) (other target : RootOutput)


/-- The complete actual accepted execution ignores the analysis marker before its first send and throughout the same adaptive continuation. -/
theorem accepted_marker (extra : NonceOutput) (response : PqxdhInitialRootLabelService.Response) :
    simulateQ (labelledFull env.source (QueryImpl.ofLift unifSpec ProbComp) selected response)
      (PqxdhInitialPrivateCurrent.accepted env (retainedKdf prior (RawCtxInitialSentinel.entry other extra) target)
        baseImpl kem attachedVerify primitives program post secret selected prepared ready) =
    simulateQ (labelledFull env.source (QueryImpl.ofLift unifSpec ProbComp) selected response)
      (PqxdhInitialPrivateCurrent.accepted env (priorKdf prior)
        baseImpl kem attachedVerify primitives program post secret selected prepared ready) := by
  funext cache
  change (simulateQ (labelledFull env.source (QueryImpl.ofLift unifSpec ProbComp) selected response)
    (PqxdhInitialPrivateCurrent.accepted env (retainedKdf prior (RawCtxInitialSentinel.entry other extra) target)
      baseImpl kem attachedVerify primitives program post secret selected prepared ready)).run cache =
    (simulateQ (labelledFull env.source (QueryImpl.ofLift unifSpec ProbComp) selected response)
      (PqxdhInitialPrivateCurrent.accepted env (priorKdf prior)
        baseImpl kem attachedVerify primitives program post secret selected prepared ready)).run cache
  rw [PqxdhInitialPrivateCurrent.accepted_response, PqxdhInitialPrivateCurrent.accepted_response, build_marker]
  simp only [simulateQ_map, PqxdhInitialSentinelPost.program]

/-- The complete unmarked accepted source executes the actual single pending builder-and-post program from its prepared state. -/
theorem actual (extra : NonceOutput) :
    simulateQ (labelledFull env.source (QueryImpl.ofLift unifSpec ProbComp) selected
      (RawCtxSelectedInitialConstructor.response64 (RawCtxInitialSentinelSampler.join second other target)))
      (PqxdhInitialPrivateCurrent.accepted env (priorKdf prior)
        baseImpl kem attachedVerify primitives program post secret selected prepared ready) =
    PqxdhInitialPendingAccepted.accepted env baseImpl kem attachedVerify primitives program post secret selected prepared ready
      prior (RawCtxInitialSentinel.entry other extra) second other target := by
  rw [← accepted_marker env baseImpl kem attachedVerify primitives program post secret selected prepared ready prior other target extra,
    PqxdhInitialPendingAccepted.actual]

/-- The production private HKDF endpoint and complete authenticated continuation instantiate the single full pending source game with no marker or callback-correspondence premise. -/
theorem production (extra : NonceOutput) :
    simulateQ (labelledFull env.source (QueryImpl.ofLift unifSpec ProbComp) selected
      (RawCtxSelectedInitialConstructor.response64 (RawCtxInitialSentinelSampler.join second other target)))
      (PqxdhInitialLegalObserver.accepted env baseImpl kem attachedVerify primitives program post secret selected prepared ready) =
    PqxdhInitialPendingAccepted.accepted env baseImpl kem attachedVerify primitives program post secret selected prepared ready
      (PqxdhJointKdf.productionStream env.source.crypto) (RawCtxInitialSentinel.entry other extra) second other target := by
  simpa only [prior_source, PqxdhInitialPrivateCurrent.accepted_source] using
    actual env baseImpl kem attachedVerify primitives program post secret selected prepared ready
      (PqxdhJointKdf.productionStream env.source.crypto) second other target extra

end Current

end BeaconcryptCore.Computational.PqxdhInitialSentinelAccepted

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSentinelAccepted.build_marker' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSentinelAccepted.build_marker

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSentinelAccepted.accepted_marker' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSentinelAccepted.accepted_marker

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSentinelAccepted.actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSentinelAccepted.actual

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSentinelAccepted.production' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSentinelAccepted.production
