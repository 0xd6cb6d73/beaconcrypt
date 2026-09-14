import BeaconcryptCore.Computational.RawCtxSelectedParentNativeContext
import BeaconcryptCore.Computational.RawCtxFamilyPendingCompiler

/-!
The retained-parent native/label source relation extends through the actual entire Server, finite role family and live-read client. It uses the concrete source receive/send equations and the original optional reader, with the same real public service. Every peer, role field, attempted-receive count, history and shared primitive effect is retained. These operational equations do not assume target freshness or a separately supplied continuation relation.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedParentFamilyMap
open RawCtxSelectedParentCalls RawCtxGenericOwnerInterpretation RawCtxGenericRoleStorage RawCtxGenericRoleFamily
open RawCtxSelectedChain RawCtxSelectedParentEntry RawCtxSelectedParentTable
open PqxdhJointKdfGame PqxdhSecretInputKdf
variable {M P I D K A Result : Type} {S B : Nat}

/-- Interpreting the exact pending label calls gives the actual retained-parent receive and send programs. -/
theorem label_calls (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (response : RatchetKdfResponse) :
    interpretedCalls (RawCtxSelectedParentCompiler.pending (Auxiliary := A) source writer prior entry response)
      RawCtxPendingOwnerQueries.calls = labelCalls source writer prior entry response := by
  simp only [interpretedCalls, RawCtxSelectedParentCompiler.pending, QueryImpl.simulateQ_compose,
    RawCtxPendingOwnerQueries.receive_call, RawCtxPendingOwnerQueries.send_call]
  exact RawCtxSelectedParentCompiler.calls_interpreted source writer prior entry response

private theorem server_interpreted {Chain : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (primitive : QueryImpl (RawCtxPendingOwnerQueries.Spec Chain) m)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxServerMixed.SourceSpec Result)
    (state : RawCtxPendingServerTails.State Chain M P) :
    simulateQ primitive (RawCtxPendingServerTails.program sender route decode client state) =
      (simulateQ (RawCtxGenericServer.serverImpl (interpretedCalls primitive RawCtxPendingOwnerQueries.calls)
        sender route decode) client).run state := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => simp only [RawCtxPendingServerTails.program, simulateQ_pure, StateT.run_pure]
  | query_bind query next ih =>
      simp only [RawCtxPendingServerTails.program, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [RawCtxGenericFamilyInterpretation.server_interpretation]
      exact bind_congr fun result => ih result.1 result.2

/-- The complete original Server continuation retains every peer and callback effect under the actual native/label retained-parent relation. -/
theorem server_program (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxServerMixed.SourceSpec Result)
    (state : RawCtxPendingServerTails.State Slot M P) :
    simulateQ (RawCtxSelectedParentNativeCompiler.pending (Auxiliary := A) source writer prior entry target)
      (RawCtxPendingServerTails.program sender route decode client (mapServer (nativeKernel target) state)) =
      Prod.map id (mapServer (nativeKernel target)) <$>
        simulateQ (RawCtxSelectedParentCompiler.pending source writer prior entry (childResponse prior entry target))
          (RawCtxPendingServerTails.program sender route decode client state) := by
  rw [server_interpreted, server_interpreted, label_calls,
    RawCtxSelectedParentNativeCompiler.calls_interpretation]
  exact RawCtxGenericServer.schedule_map (nativeKernel target)
    (labelCalls source writer prior entry (childResponse prior entry target))
    (nativeCalls source writer prior entry target) (receive_map source writer prior entry target)
    (send_map source writer prior entry target) sender route decode client state

/-- The actual entire indexed role/public continuation retains every Server, Beacon and common real public effect. -/
theorem family_program (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolRoles.SourceSpec S B) Result)
    (state : RawCtxPendingFamilyTails.State Slot M P I D K S B) :
    simulateQ (RawCtxSelectedParentNativeCompiler.pending (Auxiliary := A) source writer prior entry target)
      (RawCtxPendingFamilyTails.program sender route decode client (mapRoles (nativeKernel target) state)) =
      Prod.map id (mapRoles (nativeKernel target)) <$>
        simulateQ (RawCtxSelectedParentCompiler.pending source writer prior entry (childResponse prior entry target))
          (RawCtxPendingFamilyTails.program sender route decode client state) := by
  simp only [RawCtxPendingFamilyTails.program, RawCtxGenericFamilyInterpretation.schedule_interpretation,
    RawCtxSelectedParentNativeCompiler.calls_interpretation, label_calls,
    RawCtxSelectedParentNativeCompiler.public_interpretation]
  have publicEquation : (fun request => simulateQ
      (RawCtxSelectedParentCompiler.pending (Auxiliary := A) source writer prior entry (childResponse prior entry target))
      (RawCtxPendingOwnerQueries.publicForward request)) = RawCtxSelectedParentOwner.publicImpl source writer := by
    funext query
    simp [RawCtxSelectedParentCompiler.pending, QueryImpl.compose, RawCtxPendingOwnerQueries.publicForward,
      RawCtxPendingOwnerQueries.erase, RawCtxSelectedParentCompiler.original, OracleSpec.query]
  rw [publicEquation]
  exact RawCtxGenericFamilyFrontend.schedule_map (nativeKernel target)
    (labelCalls source writer prior entry (childResponse prior entry target))
    (nativeCalls source writer prior entry target) (RawCtxSelectedParentOwner.publicImpl source writer)
    (receive_map source writer prior entry target) (send_map source writer prior entry target)
    sender route decode client state

noncomputable def nativeLive (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) :
    QueryImpl (RawCtxPendingFamilyLiveQueries.Spec RatchetChain S B)
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp) :=
  RawCtxPendingFamilyLiveQueries.handler (RawCtxSelectedParentNativeCompiler.pending source writer prior entry target)
    (RawCtxGenericFamilyRead.nativeReader (fun kernel => ⟨kernel⟩))

noncomputable def labelLive (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) :
    QueryImpl (RawCtxPendingFamilyLiveQueries.Spec Slot S B)
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp) :=
  RawCtxPendingFamilyLiveQueries.handler
    (RawCtxSelectedParentCompiler.pending source writer prior entry (childResponse prior entry target))
    (RawCtxGenericFamilyRead.nativeReader (fun kernel => ⟨nativeKernel target kernel⟩))

/-- The original complete adaptive LIVE family client retains its actual optional native read values and full history through the retained-parent representation. -/
theorem live_program (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxPendingFamilyLiveQueries.State Slot M P I D K S B) :
    simulateQ (nativeLive (A := A) source writer prior entry target)
      (RawCtxPendingFamilyLiveTails.program sender route decode client
        (RawCtxGenericFamilyLive.mapState (nativeKernel target) state)) =
      Prod.map id (RawCtxGenericFamilyLive.mapState (nativeKernel target)) <$>
        simulateQ (labelLive source writer prior entry target)
          (RawCtxPendingFamilyLiveTails.program sender route decode client state) := by
  simp only [RawCtxPendingFamilyLiveTails.program, nativeLive, labelLive,
    RawCtxPendingFamilyLiveQueries.program_interpretation,
    RawCtxSelectedParentNativeCompiler.calls_interpretation, label_calls,
    RawCtxSelectedParentNativeCompiler.public_interpretation]
  have publicEquation : (fun request => simulateQ
      (RawCtxSelectedParentCompiler.pending (Auxiliary := A) source writer prior entry (childResponse prior entry target))
      (RawCtxPendingOwnerQueries.publicForward request)) = RawCtxSelectedParentOwner.publicImpl source writer := by
    funext query
    simp [RawCtxSelectedParentCompiler.pending, QueryImpl.compose, RawCtxPendingOwnerQueries.publicForward,
      RawCtxPendingOwnerQueries.erase, RawCtxSelectedParentCompiler.original, OracleSpec.query]
  rw [publicEquation]
  apply RawCtxGenericFamilyLive.schedule_map (nativeKernel target)
    (labelCalls source writer prior entry (childResponse prior entry target))
    (nativeCalls source writer prior entry target) (RawCtxSelectedParentOwner.publicImpl source writer)
    _ _ (receive_map source writer prior entry target) (send_map source writer prior entry target) _
    sender route decode client state
  intro request kernel
  exact congrArg pure (RawCtxGenericFamilyRead.map_value (nativeKernel target)
    (fun kernel => ⟨kernel⟩) (request, kernel))

end BeaconcryptCore.Computational.RawCtxSelectedParentFamilyMap

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentFamilyMap.label_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentFamilyMap.label_calls

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentFamilyMap.server_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentFamilyMap.server_program

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentFamilyMap.family_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentFamilyMap.family_program

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentFamilyMap.live_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentFamilyMap.live_program
