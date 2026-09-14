import BeaconcryptCore.Computational.RawCtxGenericOwnerMap

/-!
Interpreting the actual kernel calls commutes with the original whole owner frontend. These laws only move the same oracle interpreter through the source syntax; they add no functional, distribution or security premise. The same query replies, owner fields, raw validation branches, optional failures and complete ambient effects remain present, including arbitrary public interleavings.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxGenericOwnerInterpretation
open RawCtxChainOwner RawCtxGenericOwnerMap

noncomputable def interpretedCalls {Kernel ι : Type} {spec : OracleSpec ι}
    {m : Type → Type*} [Monad m] (impl : QueryImpl spec m) (calls : Calls Kernel (OracleComp spec)) : Calls Kernel m :=
  ⟨fun entry target context => simulateQ impl (calls.receive entry target context),
    fun entry context => simulateQ impl (calls.send entry context)⟩

/-- Interpreting the original raw receive calls preserves every actual validation, optional reply and owner poststate. -/
theorem raw_interpretation {Kernel Metadata ι : Type} {spec : OracleSpec ι}
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    (impl : QueryImpl spec m) (calls : Calls Kernel (OracleComp spec))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (state : State Kernel Metadata) :
    simulateQ impl ((rawReceive calls decode raw).run state) =
      (rawReceive (interpretedCalls impl calls) decode raw).run state := by
  simp only [rawReceive, StateT.run]
  by_cases empty : raw.isEmpty = true
  · simp only [empty, if_true, simulateQ_pure]
  · simp only [empty, Bool.false_eq_true, if_false]
    cases decoded : decode raw with
    | some frame =>
      by_cases valid : RawCtxReceive.ValidFrame state.expectedSender state.associatedData frame
      · simp only [valid, if_true, interpretedCalls, bind_pure_comp, simulateQ_map]
      · simp only [valid, if_false, simulateQ_pure]
    | none => simp only [simulateQ_pure]

/-- The same send interpreter preserves empty rejection, actual optional sealing and failed-seal advancement. -/
theorem send_interpretation {Kernel Metadata ι : Type} {spec : OracleSpec ι}
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    (impl : QueryImpl spec m) (calls : Calls Kernel (OracleComp spec))
    (sender : Std.U64) (plaintext : Pqxdh.Bytes) (state : State Kernel Metadata) :
    simulateQ impl ((sendOwner calls sender plaintext).run state) =
      (sendOwner (interpretedCalls impl calls) sender plaintext).run state := by
  simp only [sendOwner, StateT.run]
  by_cases empty : plaintext.isEmpty = true
  · simp only [empty, if_true, simulateQ_pure]
  · simp only [empty, Bool.false_eq_true, if_false, interpretedCalls, bind_pure_comp, simulateQ_map]

/-- The complete original mixed-owner step uses exactly the separately interpreted source callbacks. -/
theorem owner_interpretation {Kernel Metadata ι : Type} {spec : OracleSpec ι}
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    (impl : QueryImpl spec m) (calls : Calls Kernel (OracleComp spec))
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : State Kernel Metadata) :
    simulateQ impl ((ownerImpl calls sender decode query).run state) =
      (ownerImpl (interpretedCalls impl calls) sender decode query).run state := by
  cases query with
  | inl plaintext => exact send_interpretation impl calls sender plaintext state
  | inr raw => exact raw_interpretation impl calls decode raw state

/-- Public callbacks are interpreted by the same primitive handler without altering owner fields or replies. -/
theorem public_interpretation {Kernel Metadata ι κ : Type} {spec : OracleSpec ι} {publicSpec : OracleSpec κ}
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    (impl : QueryImpl spec m) (calls : Calls Kernel (OracleComp spec))
    (publicImpl : QueryImpl publicSpec (OracleComp spec))
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxMixedOwner.SourceSpec + publicSpec).Domain) (state : State Kernel Metadata) :
    simulateQ impl ((publicOwner calls publicImpl sender decode query).run state) =
      (publicOwner (interpretedCalls impl calls) (fun request => simulateQ impl (publicImpl request))
        sender decode query).run state := by
  cases query with
  | inl request => exact owner_interpretation impl calls sender decode request state
  | inr request => simp only [publicOwner, StateT.run, bind_pure_comp, simulateQ_map]

/-- Every complete adaptive original send/raw/public execution equals the same frontend over separately interpreted calls. -/
theorem public_schedule_interpretation {Kernel Metadata Result ι κ : Type}
    {spec : OracleSpec ι} {publicSpec : OracleSpec κ}
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    (impl : QueryImpl spec m) (calls : Calls Kernel (OracleComp spec))
    (publicImpl : QueryImpl publicSpec (OracleComp spec))
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxMixedOwner.SourceSpec + publicSpec) Result) (state : State Kernel Metadata) :
    simulateQ impl ((simulateQ (publicOwner calls publicImpl sender decode) client).run state) =
      (simulateQ (publicOwner (interpretedCalls impl calls) (fun request => simulateQ impl (publicImpl request))
        sender decode) client).run state := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [public_interpretation]
    exact bind_congr fun result => ih result.1 result.2

end BeaconcryptCore.Computational.RawCtxGenericOwnerInterpretation

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericOwnerInterpretation.raw_interpretation' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericOwnerInterpretation.raw_interpretation

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericOwnerInterpretation.send_interpretation' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericOwnerInterpretation.send_interpretation

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericOwnerInterpretation.owner_interpretation' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericOwnerInterpretation.owner_interpretation

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericOwnerInterpretation.public_interpretation' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericOwnerInterpretation.public_interpretation

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericOwnerInterpretation.public_schedule_interpretation' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericOwnerInterpretation.public_schedule_interpretation
