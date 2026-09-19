import BeaconcryptCore.Computational.PqxdhInitialGenericRecords
import BeaconcryptCore.Computational.PqxdhInitialGenericProtocolBuilder

/-!
Concrete retained-parent receive/send equations discharge the complete current record schedule. All public services remain the real source backend. Native reads still return their original bytes in this representation intermediate; the separate masked-read/freshness comparison constructs the hidden-input observer and charges actual candidate exposures.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSelectedRecords
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhInitialGenericProtocolBuilder
variable {M P I D K A Result : Type} {S B : Nat}

noncomputable def backend (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry) (target : RootOutput) :
    QueryImpl RawCtxServerServices.BackendSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp) :=
  RawCtxServerServices.backendImpl source writer (retainedKdf prior entry target)

/-- The private projection is exactly the already verified retained-parent native backend, with the original shared primitive effects. -/
theorem native_backend (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry) (target : RootOutput) :
    backend (A := A) source writer prior entry target ∘ₛ RawCtxServerServices.nativeLift =
      RawCtxSelectedParentNativeBackend.backend source writer prior entry target := by
  rw [backend, RawCtxServerServices.native_interpretation, ← retained_backend]

/-- The actual retained backend discharges the full private receive equation for a selected kernel; no callback compatibility is assumed. -/
theorem receive_native (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry) (target : RootOutput)
    (kernel : RawCtxSelectedChain.Kernel) (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    simulateQ (((backend (A := A) source writer prior entry target ∘ₛ RawCtxServerServices.nativeLift) ∘ₛ
      RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter)
      (RawCtxOwnerOracle.receive (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target) kernel) sequence context) =
      (fun result => (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target) result.1, result.2)) <$>
        (RawCtxSelectedParentCalls.labelCalls source writer prior entry
          (RawCtxSelectedParentCalls.childResponse prior entry target)).receive kernel sequence context := by
  rw [native_backend]
  have received := RawCtxSelectedParentNativeBackend.receive_realized (Auxiliary := A) source writer prior entry target
    (RawCtxSelectedParentCalls.nativeKernel target kernel) sequence context
  rw [RawCtxSelectedParentCalls.receive_map] at received
  simpa only [Functor.map_map, RawCtxSelectedChain.nativeKernel, RawCtxSelectedParentCalls.nativeKernel,
    Prod.map_fst, Prod.map_snd, id_eq] using received

/-- The actual retained backend discharges the full private send equation before any material reaches the original seal callback. -/
theorem send_native (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry) (target : RootOutput)
    (kernel : RawCtxSelectedChain.Kernel) (context : RawCtxSourceSend.SealContext) :
    simulateQ (((backend (A := A) source writer prior entry target ∘ₛ RawCtxServerServices.nativeLift) ∘ₛ
      RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
      (RawCtxSourceSend.send (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target) kernel) context) =
      (fun result => (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target) result.1, result.2)) <$>
        (RawCtxSelectedParentCalls.labelCalls source writer prior entry
          (RawCtxSelectedParentCalls.childResponse prior entry target)).send kernel context := by
  rw [native_backend]
  exact PqxdhInitialGenericPublication.selected_send source writer prior entry target kernel context

/-- The complete actual current record operation uses the same private retained response, real public service and original optional read; every callback equation is discharged. -/
theorem record (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry) (target : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (state : PqxdhInitialGenericProtocol.State RawCtxSelectedChain.Kernel M P I D K A S B) :
    (PqxdhInitialPrivateKdf.records source writer (retainedKdf prior entry target) sender route decode query).run
      (PqxdhInitialGenericProtocol.native (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)) state) =
      Prod.map id (PqxdhInitialGenericProtocol.native (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target))) <$>
        (PqxdhInitialGenericRecords.records
          (RawCtxSelectedParentCalls.labelCalls source writer prior entry (RawCtxSelectedParentCalls.childResponse prior entry target))
          (backend source writer prior entry target ∘ₛ RawCtxServerServices.publicLift)
          (RawCtxGenericFamilyRead.nativeReader (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)))
          sender route decode query).run state := by
  rw [← PqxdhInitialGenericRecords.native_source]
  exact PqxdhInitialGenericRecords.record_native _ _ _
    (receive_native source writer prior entry target) (send_native source writer prior entry target)
    sender route decode query state

/-- Every adaptive original current record schedule retains its full optional replies, roles and source history under the concrete retained-parent interpretation. -/
theorem schedule (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry) (target : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : PqxdhInitialGenericProtocol.State RawCtxSelectedChain.Kernel M P I D K A S B) :
    (simulateQ (PqxdhInitialPrivateKdf.records source writer (retainedKdf prior entry target) sender route decode) client).run
      (PqxdhInitialGenericProtocol.native (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)) state) =
      Prod.map id (PqxdhInitialGenericProtocol.native (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target))) <$>
        (simulateQ (PqxdhInitialGenericRecords.records
          (RawCtxSelectedParentCalls.labelCalls source writer prior entry (RawCtxSelectedParentCalls.childResponse prior entry target))
          (backend source writer prior entry target ∘ₛ RawCtxServerServices.publicLift)
          (RawCtxGenericFamilyRead.nativeReader (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)))
          sender route decode) client).run state := by
  exact (map_run_simulateQ_eq_of_query_map_eq _ _
    (PqxdhInitialGenericProtocol.native (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)))
    (fun query before => (record source writer prior entry target sender route decode query before).symm)
    client state).symm

end BeaconcryptCore.Computational.PqxdhInitialSelectedRecords

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSelectedRecords.native_backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSelectedRecords.native_backend
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSelectedRecords.receive_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSelectedRecords.receive_native
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSelectedRecords.send_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSelectedRecords.send_native
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSelectedRecords.record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSelectedRecords.record
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSelectedRecords.schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSelectedRecords.schedule
