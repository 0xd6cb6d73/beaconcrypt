import BeaconcryptCore.Computational.PqxdhInitialSentinelBeacon
import BeaconcryptCore.Computational.PqxdhInitialPostInterpretation

/-!
The initializer marker is removed through every actual post request, retaining the entire shared, identity and root-cache distribution. The proof uses typed original record and Beacon calls, including arbitrary adaptive scheduling and attempted registrations.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSentinelPost
open PqxdhJointKdfGame PqxdhKemIndCca PqxdhCorrelatedExpand PqxdhPhase2SourceAux
open PqxdhPhase1AcceptanceOracle PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPrivateKemSource
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhCorrelatedExtractFamily PqxdhCorrelatedExpandHybrid
open PqxdhInitialRootLabelService PqxdhInitialBeaconAmbient PqxdhInitialGenericProtocolBuilder
open RawCtxSelectedParentTable PqxdhInitialSentinelSource
variable {ι M P I D K X Response A KemSK Result : Type} {baseSpec : OracleSpec ι} {S B : Nat}

section Current
variable
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (selected : Message) (response : PqxdhInitialRootLabelService.Response)


/-- Evaluating the entire original first-receive owner preserves its complete state after removing the initializer marker. -/
theorem owner (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (other target : RootOutput) (extra : NonceOutput)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (before : RawCtxBeaconLifecycle.State (PqxdhGeneratedBeaconState.IdentityHandle I) D
      (PqxdhGeneratedBeaconState.KemHandle K)) :
    PqxdhInitialPostInterpretation.work
      (labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp) selected response)
      (PqxdhInitialCurrentPost.owner attachedVerify primitives count fixed
        (retainedKdf prior (RawCtxInitialSentinel.entry other extra) target)
        localImpl baseImpl kem secret challenge decode raw before) =
    PqxdhInitialPostInterpretation.work
      (labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp) selected response)
      (PqxdhInitialCurrentPost.owner attachedVerify primitives count fixed
        (priorKdf prior) localImpl baseImpl kem secret challenge decode raw before) := by
  funext state
  simp only [PqxdhInitialPostInterpretation.work, PqxdhInitialCurrentPost.owner,
    QueryImpl.simulateQ_mapStateTBase_run]
  exact congrFun (PqxdhInitialSentinelBeacon.owner_marker attachedVerify primitives count fixed
    localImpl baseImpl kem secret challenge selected response writer prior other target extra decode raw before) state

/-- Every adaptive original post request has the same complete distribution after removing the initializer marker, including identity/CCA selectors and attempted Beacon completion. -/
theorem program (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (other target : RootOutput) (extra : NonceOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (PqxdhPhase2SourceScheduler.Spec baseSpec S B) Result)
    (state : PqxdhPhase2PostScheduler.State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count) :
    simulateQ (labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp) selected response)
      ((simulateQ (PqxdhInitialPrivateBeacon.target attachedVerify primitives count fixed
        (retainedKdf prior (RawCtxInitialSentinel.entry other extra) target) localImpl writer sender route decode
        baseImpl kem secret challenge) client).run state) =
    simulateQ (labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp) selected response)
      ((simulateQ (PqxdhInitialPrivateBeacon.target attachedVerify primitives count fixed
        (priorKdf prior) localImpl writer sender route decode baseImpl kem secret challenge) client).run state) := by
  rw [← PqxdhInitialCurrentPost.source, ← PqxdhInitialCurrentPost.source,
    PqxdhInitialPostInterpretation.native_schedule, PqxdhInitialPostInterpretation.native_schedule]
  simp only [owner attachedVerify primitives count fixed localImpl baseImpl kem secret challenge selected response writer]
  delta PqxdhInitialCurrentPost.records
  rw [PqxdhInitialSentinelRecords.records]

end Current
end BeaconcryptCore.Computational.PqxdhInitialSentinelPost

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSentinelPost.owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSentinelPost.owner

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSentinelPost.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSentinelPost.program
