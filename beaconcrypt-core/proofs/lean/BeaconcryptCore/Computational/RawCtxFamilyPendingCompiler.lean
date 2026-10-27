import BeaconcryptCore.Computational.RawCtxFamilySourceFreshness
import BeaconcryptCore.Computational.RawCtxSelectedFamilyContext

/-!
The enriched pending family interface erases only the private pending payload and original read owner tag already retained by the source history. Its non-read callbacks remain the actual receive/send/public capability. The original complete family client and the selected in-progress completion compile to the same old primitive/read program. No target bytes, source compatibility assumption or resource premise is added.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxFamilyPendingCompiler
open RawCtxSelectedChain RawCtxGenericOwnerInterpretation
open RawCtxFamilySourceFreshness
variable {M P I D K Result Value : Type} {S B : Nat}

noncomputable def calls : RawCtxChainOwner.Calls Kernel (OracleComp PrimitiveSpec) :=
  RawCtxPendingOwnerQueries.originalCalls

def publicCalls : QueryImpl RawCtxServerServices.PublicSpec (OracleComp PrimitiveSpec) :=
  RawCtxPendingOwnerQueries.originalPublic

def primitive : QueryImpl (RawCtxPendingOwnerQueries.Spec Slot) (OracleComp Spec) :=
  RawCtxSelectedLiveCompiler.primitiveForward ∘ₛ RawCtxPendingOwnerQueries.erase

noncomputable def live : QueryImpl (RawCtxPendingFamilyLiveQueries.Spec Slot S B) (OracleComp Spec) :=
  RawCtxPendingFamilyLiveQueries.handler primitive RawCtxFamilyReadCompiler.compiler

/-- Erasing enriched pending receive/send calls gives the actual original chain calls, including every attempted opening or sealing operation. -/
theorem calls_erased : interpretedCalls RawCtxPendingOwnerQueries.erase RawCtxPendingOwnerQueries.calls = calls := by
  simp only [interpretedCalls, RawCtxPendingOwnerQueries.receive_call, RawCtxPendingOwnerQueries.send_call, calls]

/-- The forwarded pending calls retain exactly the original public primitive capability. -/
theorem calls_forwarded : interpretedCalls primitive RawCtxPendingOwnerQueries.calls =
    interpretedCalls RawCtxSelectedLiveCompiler.primitiveForward calls := by
  simp only [interpretedCalls, primitive, QueryImpl.simulateQ_compose,
    RawCtxPendingOwnerQueries.receive_call, RawCtxPendingOwnerQueries.send_call, calls]

/-- The complete original pending LIVE family program is exactly the source compiler used by the derived freshness invariant. -/
theorem program_source (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : State M P I D K S B) :
    simulateQ live (RawCtxPendingFamilyLiveTails.program sender route decode client state) =
      (simulateQ (compiler calls publicCalls sender route decode) client).run state := by
  rw [RawCtxPendingFamilyLiveTails.program, live, RawCtxPendingFamilyLiveQueries.program_interpretation,
    calls_forwarded, compiler_source]
  rfl

noncomputable def completion (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (history : RawCtxProtocolReveals.History S B)
    (outside : Value → OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (work : OracleComp PrimitiveSpec (Value × Roles M P I D K S B)) :
    OracleComp Spec (Result × State M P I D K S B) := do
  let result ← simulateQ RawCtxSelectedLiveCompiler.primitiveForward work
  (simulateQ (compiler calls publicCalls sender route decode) (outside result.1)).run
    (result.2, RawCtxProtocolReveals.tick history)

/-- The in-progress non-read family completion finishes before the same original outside LIVE client and its single history tick. -/
theorem lift_source (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (history : RawCtxProtocolReveals.History S B)
    (outside : Value → OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (work : OracleComp (RawCtxPendingOwnerQueries.Spec Slot) (Value × Roles M P I D K S B)) :
    simulateQ live (RawCtxPendingFamilyLiveTails.liftFamily sender route decode history outside work) =
      completion sender route decode history outside (simulateQ RawCtxPendingOwnerQueries.erase work) := by
  simp only [RawCtxPendingFamilyLiveTails.liftFamily, simulateQ_bind,
    ← QueryImpl.simulateQ_compose, live, RawCtxPendingFamilyLiveQueries.primitive_handler]
  simp only [completion, primitive, QueryImpl.simulateQ_compose]
  exact bind_congr fun result => program_source sender route decode (outside result.1)
    (result.2, RawCtxProtocolReveals.tick history)

/-- The actual material-only selected family context has this exact completion-prefix and outside-client factorization. -/
theorem stopped_source (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (request : (RawCtxProtocolRoles.SourceSpec S B).Domain)
    (history : RawCtxProtocolReveals.History S B)
    (outside : (RawCtxProtocolRoles.SourceSpec S B).Range request → OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (inner : RawCtxSelectedFamilyContext.FamilyContext M P I D K
      ((RawCtxProtocolRoles.SourceSpec S B).Range request) S B) (value : PqxdhOrderedChainHybrids.Material) :
    simulateQ live (RawCtxSelectedFamilyContext.stopped sender route decode
      (.family request history outside inner) value) =
      completion sender route decode history outside (simulateQ RawCtxPendingOwnerQueries.erase
        (RawCtxSelectedFamilyContext.familyStopped sender route decode inner value)) :=
  lift_source sender route decode history outside _

end BeaconcryptCore.Computational.RawCtxFamilyPendingCompiler

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyPendingCompiler.calls_erased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyPendingCompiler.calls_erased

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyPendingCompiler.calls_forwarded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyPendingCompiler.calls_forwarded

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyPendingCompiler.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyPendingCompiler.program_source

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyPendingCompiler.lift_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyPendingCompiler.lift_source

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyPendingCompiler.stopped_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyPendingCompiler.stopped_source
