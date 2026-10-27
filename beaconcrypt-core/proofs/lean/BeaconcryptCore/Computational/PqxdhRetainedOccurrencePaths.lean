import BeaconcryptCore.Computational.PqxdhRetainedOccurrenceInterpreter

/-! Concrete retained completions carry the existing source-generated installation evidence. The annotation is recovered by support of its exact erasure, with the original Boolean origin trace and all operational state unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRetainedOccurrencePaths
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhInitialNativeRetained PqxdhInitialBeaconAmbient PqxdhInitialReceiptConstruction
open PqxdhRetainedOccurrenceInterpreter
variable {ι M P I D K X Response Origin A N Result AD PT CT : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (prior : RawCtxSelectedParentTable.Prior) (selected : Message) (previousRoot : RootOutput)
  (response64 : PqxdhInitialRootLabelService.Response)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
    (Ambient A N RootOracle.QueryCache))
  (application : Response → Ambient A N RootOracle.QueryCache (Option Pqxdh.Bytes))
  (selector : QueryImpl extra (Ambient A N RootOracle.QueryCache))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N RootOracle.QueryCache))
  (mark : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared → Origin) (origin : Origin)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
  (post : RustM (Option PqxdhServerRegistrationPublication.Response) →
    OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
local notation "external" => PqxdhInitialNativeAudit.external pre application
  (PqxdhInitialNativeInitializer.initial source selected previousRoot response64) selector aux
local notation "impl" => retained (S := S) (B := B) source writer prior external
local notation "Front" => PqxdhInitialPendingPost.Front RatchetChain M P I D K S B
local notation "Trace" => PqxdhInitialOriginPost.Trace Origin S B
local notation "Evidence" => PqxdhInitialInstallOccurrence.Trace RatchetChain Response PqxdhPhase2DecapsulationRouting.Shared S B

/-- The complete occurrence-annotated sequence erases to the original retained Builder and adaptive Post, with every original result, origin marker and backend field preserved. -/
theorem sequence_erase (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain))
    (entry : Front × Trace) (state : RetainedState A N RootOracle.QueryCache) :
    Prod.map (Prod.map id Prod.fst) id <$>
      (simulateQ impl ((PqxdhInitialInstallOccurrence.sequence source initial mark origin sender route decode
        index metadata ready post).run (entry, PqxdhInitialInstallOccurrence.empty))).run state =
    (simulateQ impl ((PqxdhInitialOriginPost.sequence source initial mark origin sender route decode
      index metadata ready post).run entry)).run state := by
  rw [← PqxdhInitialInstallOccurrence.sequence_erase source initial mark origin sender route decode
    index metadata ready post (entry, PqxdhInitialInstallOccurrence.empty), simulateQ_map, StateT.run_map]
  rfl

/-- The actual retained initializer and all original callbacks discharge the existing occurrence-path invariant for the complete annotated source sequence. -/
theorem annotated_holds (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (serverResponse : pqxdh.concrete.InitialRatchetKdfResponse)
    (entry : Front × Trace) (state : RetainedState A N RootOracle.QueryCache)
    (result : (Result × ((Front × Trace) × Evidence)) × RetainedState A N RootOracle.QueryCache)
    (supported : result ∈ support ((simulateQ impl
      ((PqxdhInitialInstallOccurrence.sequence source
        (ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false serverResponse)
        mark origin sender route decode index metadata ready post).run
          (entry, PqxdhInitialInstallOccurrence.empty))).run state)) :
    PqxdhInitialOccurrencePaths.Holds cr prior result.1.2.1.1 result.1.2.2 := by
  apply PqxdhInitialOccurrencePaths.sequence_holds source writer prior selected previousRoot response64
    (fun query => ambient (pre query)) (fun reply => ambient (application reply))
    (fun query => ambient (selector query)) (fun query => ambient (aux query))
    cr serverResponse mark origin sender route decode index metadata ready post entry
    (reassociate state) (Prod.map id reassociate result)
  rw [← source_program source writer prior selected previousRoot response64 pre application selector aux]
  simp only [support_map, Set.mem_image]
  exact ⟨result, supported, rfl⟩

/-- Every supported original retained completion has an actual source occurrence annotation with the same result, original Boolean trace and backend state. Its path invariant is derived from literal initialization, not assumed for arbitrary preexisting owners. -/
theorem sequence_supported (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (serverResponse : pqxdh.concrete.InitialRatchetKdfResponse)
    (entry : Front × Trace) (state : RetainedState A N RootOracle.QueryCache)
    (result : (Result × (Front × Trace)) × RetainedState A N RootOracle.QueryCache)
    (supported : result ∈ support ((simulateQ impl
      ((PqxdhInitialOriginPost.sequence source
        (ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false serverResponse)
        mark origin sender route decode index metadata ready post).run entry)).run state)) :
    ∃ evidence : Evidence,
      ((result.1.1, (result.1.2, evidence)), result.2) ∈ support ((simulateQ impl
        ((PqxdhInitialInstallOccurrence.sequence source
          (ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false serverResponse)
          mark origin sender route decode index metadata ready post).run
            (entry, PqxdhInitialInstallOccurrence.empty))).run state) ∧
      PqxdhInitialOccurrencePaths.Holds cr prior result.1.2.1 evidence := by
  rw [← sequence_erase source writer prior selected previousRoot response64 pre application selector aux
    mark origin sender route decode index metadata ready post] at supported
  simp only [support_map, Set.mem_image] at supported
  obtain ⟨⟨⟨value, saved, evidence⟩, after⟩, actual, same⟩ := supported
  cases same
  exact ⟨evidence, actual, annotated_holds source writer prior selected previousRoot response64
    pre application selector aux mark origin sender route decode index metadata ready post
    cr serverResponse entry state _ actual⟩

end BeaconcryptCore.Computational.PqxdhRetainedOccurrencePaths

/-- info: 'BeaconcryptCore.Computational.PqxdhRetainedOccurrencePaths.sequence_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRetainedOccurrencePaths.sequence_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhRetainedOccurrencePaths.annotated_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRetainedOccurrencePaths.annotated_holds

/-- info: 'BeaconcryptCore.Computational.PqxdhRetainedOccurrencePaths.sequence_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRetainedOccurrencePaths.sequence_supported
