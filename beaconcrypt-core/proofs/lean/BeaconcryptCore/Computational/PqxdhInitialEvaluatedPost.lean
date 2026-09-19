import BeaconcryptCore.Computational.PqxdhInitialEvaluatedRecords
import BeaconcryptCore.Computational.PqxdhInitialCurrentBeacon

/-!
The complete current post continuation is evaluated with the shared initializer cache and represented with selected chain slots. This exact source equality includes records, the private identity/CCA selector and every attempted Beacon finish. It is an operational equation: native reveal interpretation still contains the selected chain and must be replaced by the checked freshness compiler before using an ordinary primitive reduction.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialEvaluatedPost
open PqxdhJointKdfGame PqxdhKemIndCca PqxdhPhase2SourceAux PqxdhPhase1AcceptanceOracle
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPrivateKemSource PqxdhCorrelatedExtractFamily
open PqxdhInitialRootLabelService PqxdhInitialGenericProtocolBuilder PqxdhCorrelatedExpand
variable {ι M P I D K X Response A KemSK Result : Type} {baseSpec : OracleSpec ι} {S B : Nat}

section Current
variable
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (selected : Message) (second : Bool) (other target : PqxdhSecretInputKdf.RootOutput)

noncomputable def records : QueryImpl (RawCtxProtocolReveals.SourceSpec S B)
    (StateT (PqxdhInitialGenericProtocol.State RawCtxSelectedChain.Kernel M P
      (PqxdhGeneratedBeaconState.IdentityHandle I) D (PqxdhGeneratedBeaconState.KemHandle K) A S B)
      (StateT RootOracle.QueryCache ProbComp)) :=
  PqxdhInitialEvaluatedRecords.lift (PqxdhInitialGenericRecords.records
    (RawCtxSelectedParentCalls.labelCalls fixed writer prior entry (RawCtxSelectedParentCalls.childResponse prior entry target))
    (PqxdhInitialSelectedRecords.backend fixed writer prior entry target ∘ₛ RawCtxServerServices.publicLift)
    (RawCtxGenericFamilyRead.nativeReader (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)))
    sender route decode)

noncomputable def handler : QueryImpl (PqxdhPhase2SourceScheduler.Spec baseSpec S B)
    (StateT (PqxdhInitialGenericPost.State RawCtxSelectedChain.Kernel M P
      (PqxdhGeneratedBeaconState.IdentityHandle I) D (PqxdhGeneratedBeaconState.KemHandle K) A (BareState count) S B)
      (StateT RootOracle.QueryCache ProbComp)) :=
  PqxdhInitialGenericPost.post (records fixed writer sender route decode prior entry target)
    ((labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp) selected
      (RawCtxSelectedInitialConstructor.response64 (RawCtxInitialSentinelSampler.join second other target))).mapStateTBase
        (PqxdhInitialCurrentPost.selector attachedVerify primitives count baseImpl kem secret challenge))
    (PqxdhInitialCurrentBeacon.owner attachedVerify primitives count fixed localImpl baseImpl kem secret challenge
      prior entry selected second other writer (RawCtxSelectedParentCalls.childResponse prior entry target) decode)

/-- The actual evaluated current source continuation has this complete retained-slot distribution, including the root cache, private identity state, every optional reply and original operation order. -/
theorem source
    (client : OracleComp (PqxdhPhase2SourceScheduler.Spec baseSpec S B) Result)
    (state : PqxdhInitialGenericPost.State RawCtxSelectedChain.Kernel M P
      (PqxdhGeneratedBeaconState.IdentityHandle I) D (PqxdhGeneratedBeaconState.KemHandle K) A (BareState count) S B) :
    simulateQ (labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp) selected
      (RawCtxSelectedInitialConstructor.response64 (RawCtxInitialSentinelSampler.join second other target)))
      ((simulateQ (PqxdhInitialPrivateBeacon.target attachedVerify primitives count fixed (retainedKdf prior entry target)
        localImpl writer sender route decode baseImpl kem secret challenge) client).run
          (PqxdhInitialGenericPost.native (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)) state)) =
      Prod.map id (PqxdhInitialGenericPost.native (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target))) <$>
        (simulateQ (handler attachedVerify primitives count fixed localImpl writer sender route decode baseImpl kem secret challenge
          prior entry selected second other target) client).run state := by
  rw [← PqxdhInitialCurrentPost.source, PqxdhInitialPostInterpretation.native_schedule]
  unfold handler
  apply PqxdhInitialGenericPost.schedule_native
  · intro query before
    rw [PqxdhInitialEvaluatedRecords.records_source]
    exact PqxdhInitialEvaluatedRecords.selected_record fixed writer prior entry target sender route decode query before
  · intro raw before
    funext ambient
    simp only [PqxdhInitialPostInterpretation.work, PqxdhInitialCurrentPost.owner, QueryImpl.simulateQ_mapStateTBase_run]
    exact congrFun (PqxdhInitialCurrentBeacon.source_owner attachedVerify primitives count fixed localImpl baseImpl kem secret challenge prior entry selected second other target writer decode raw before) ambient

end Current
end BeaconcryptCore.Computational.PqxdhInitialEvaluatedPost

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialEvaluatedPost.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialEvaluatedPost.source
