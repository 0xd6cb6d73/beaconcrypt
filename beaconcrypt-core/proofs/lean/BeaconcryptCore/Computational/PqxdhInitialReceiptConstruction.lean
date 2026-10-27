import BeaconcryptCore.Computational.PqxdhInitialBuilderReceipt
import BeaconcryptCore.Computational.PqxdhInitialFinishReceipt
import BeaconcryptCore.Computational.PqxdhInitialKernelConstruction

/-!
Actual receipt consumers use the supplied Server initializer and the retained Beacon initializer. Every recorded initial kernel is the literal native zero-state constructor at its two exact directional chains. No arbitrary callback-initialization premise, distinctness assumption or chain-distribution assumption is used.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialReceiptConstruction
open PqxdhInitialPendingPost PqxdhInitialKernelConstruction
variable {ι ξ M P I D K X Response Shared Auxiliary AD PT CT : Type}
variable {extra : OracleSpec ι} {base : OracleSpec.{0, 0} ξ} {S B : Nat}

/-- A receipt from the complete actually interpreted Server Builder contains the exact zero-state source kernel and is reachable under any fixed retained ratchet interpreter. -/
theorem server (impl : QueryImpl (Spec extra RatchetChain I D K X Response Shared S B) (StateT Auxiliary (OracleComp base)))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (response : pqxdh.concrete.InitialRatchetKdfResponse)
    (sender : M → Std.U64) (index : Fin S) (metadata : P)
    (input : PqxdhPrivateAcceptedRoot.Ready) (before : Front RatchetChain M P I D K S B) (state : Auxiliary)
    (result : ((RustM (Option PqxdhServerRegistrationPublication.Response) ×
      Option (PqxdhInitialBuilderReceipt.Receipt (KernelOf RatchetChain))) × Front RatchetChain M P I D K S B) × Auxiliary)
    (supported : result ∈ support ((simulateQ impl ((PqxdhInitialBuilderReceipt.build source
      (ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false response)
      sender index metadata input).run before)).run state))
    (receipt : PqxdhInitialBuilderReceipt.Receipt (KernelOf RatchetChain)) (recorded : result.1.1.2 = some receipt)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) :
    ConcreteRatchetKernel.new receipt.initial.send_chain receipt.initial.receive_chain = .ok ⟨receipt.initial⟩ ∧
      RoleReachable cr receipt.initial.send_chain receipt.initial.receive_chain ⟨receipt.initial⟩ := by
  have initialized := PqxdhInitialBuilderReceipt.build_initialized impl source _ sender index metadata input
    before state result supported receipt recorded
  obtain ⟨_, kernel, _, created, _⟩ := PqxdhInitialSuppliedPositions.pair_positioned source.crypto response
  have same : kernel.refined = receipt.initial := by
    simpa only [created, RawCtxMaterialInterpretation.rust_map_ok, RustM.ok.injEq] using initialized
  simpa only [← same] using And.intro (supplied_new false response kernel created)
    (supplied_reachable cr false response kernel created)

abbrev InitialState (A N : Type) :=
  (RawCtxSharedPrimitive.SharedState A × N) × PqxdhCorrelatedExpand.RootOracle.QueryCache

/-- Tuple reassociation and omission of the separate audit return expose the actual retained optional initializer callback. -/
noncomputable def initial {A N : Type} (fixed : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (selected : PqxdhCorrelatedExtractFamily.Message) (previousRoot : PqxdhSecretInputKdf.RootOutput)
    (response : PqxdhInitialRootLabelService.Response)
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared) :
    StateT (InitialState A N) ProbComp (Option (KernelOf RatchetChain)) := fun state =>
  (fun result => (result.1.1.2, (result.1.2, result.2))) <$>
    ((PqxdhInitialNativeInitializer.initial fixed selected previousRoot response secrets state.1).run state.2)

/-- The concrete optional initializer supplies a literal zero-state kernel under every supported cache reply, retaining the actual complete state. -/
theorem initial_constructed {A N : Type}
    (fixed : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (selected : PqxdhCorrelatedExtractFamily.Message) (previousRoot : PqxdhSecretInputKdf.RootOutput)
    (response : PqxdhInitialRootLabelService.Response)
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (before after : InitialState A N) (kernel : KernelOf RatchetChain)
    (supported : (some kernel, after) ∈ support ((initial fixed selected previousRoot response secrets).run before)) :
    ConcreteRatchetKernel.new kernel.send_chain kernel.receive_chain = .ok ⟨kernel⟩ ∧
      RoleReachable cr kernel.send_chain kernel.receive_chain ⟨kernel⟩ := by
  simp only [initial, StateT.run, support_map] at supported
  obtain ⟨original, reached, same⟩ := supported
  obtain ⟨reply, returned, _, created, reachable⟩ :=
    retained_supported fixed selected previousRoot response secrets cr before.1 before.2 original reached
  have kernelSame : (PqxdhInitialRootAudit.kernel reply).refined = kernel := by
    have optional := congrArg (fun value => value.1) same
    simpa only [returned, Option.some.injEq] using optional
  simpa only [← kernelSame] using And.intro created reachable

/-- The complete Beacon finish records the actual retained initializer before its getter and first receive. A later rejection cannot turn that initial kernel into an arbitrary callback value. -/
theorem beacon {A N Origin : Type}
    (fixed : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (selected : PqxdhCorrelatedExtractFamily.Message) (previousRoot : PqxdhSecretInputKdf.RootOutput)
    (response : PqxdhInitialRootLabelService.Response)
    (mark : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared → Origin)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (InitialState A N) ProbComp))
    (calls : RawCtxChainOwner.Calls (KernelOf RatchetChain) (StateT (InitialState A N) ProbComp))
    (application : Response → StateT (InitialState A N) ProbComp (Option Pqxdh.Bytes))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (entry : RawCtxGenericRoleStorage.BeaconState (KernelOf RatchetChain) I D K) (before : InitialState A N)
    (result : PqxdhInitialFinishReceipt.Result (KernelOf RatchetChain) Origin I D K Response PqxdhPhase2DecapsulationRouting.Shared × InitialState A N)
    (supported : result ∈ support ((PqxdhInitialFinishReceipt.owner mark pre calls application
      (initial fixed selected previousRoot response) decode raw entry).run before))
    (receipt : PqxdhInitialFinishReceipt.Receipt (KernelOf RatchetChain) Response PqxdhPhase2DecapsulationRouting.Shared)
    (recorded : result.1.2 = some receipt)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) :
    ConcreteRatchetKernel.new receipt.initial.send_chain receipt.initial.receive_chain = .ok ⟨receipt.initial⟩ ∧
      RoleReachable cr receipt.initial.send_chain receipt.initial.receive_chain ⟨receipt.initial⟩ := by
  obtain ⟨_, _, _, _, atPrepared, atInitial, _, _, _, initialized, _, _⟩ :=
    PqxdhInitialFinishReceipt.owner_origin mark pre calls application (initial fixed selected previousRoot response)
      decode raw entry before result supported receipt recorded
  exact initial_constructed fixed selected previousRoot response receipt.prepared.root cr
    atPrepared atInitial receipt.initial initialized

end BeaconcryptCore.Computational.PqxdhInitialReceiptConstruction

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialReceiptConstruction.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialReceiptConstruction.server

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialReceiptConstruction.initial_constructed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialReceiptConstruction.initial_constructed

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialReceiptConstruction.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialReceiptConstruction.beacon
