import BeaconcryptCore.Computational.PqxdhLaterSavedOutsideSupport

/-! The actual saved compiler preserves all-reply properties of its source outside program, including optional refusals and complete state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterSavedCompilerSupport

/-- Successful optional compilation returns a value from the original all-reply program. Refusal is not turned into a reply. -/
theorem optional_support {ι Result : Type} {spec : OracleSpec.{0, 0} ι}
    (client : OracleComp spec Result) (value : Result)
    (supported : some value ∈ support (RawCtxSelectedFamilyNonceCoupling.optionalClient client)) :
    value ∈ support client := by
  induction client using OracleComp.inductionOn with
  | pure result =>
      change some value ∈ support (pure (some result) : OracleComp _ _) at supported
      have same := Option.some.inj ((mem_support_pure_iff _ _).mp supported)
      exact (mem_support_pure_iff _ _).2 same
  | query_bind query next ih =>
      rw [PqxdhFirstRecordConfidentiality.optionalClient_bind, mem_support_bind_iff] at supported
      obtain ⟨_ | reply, _, returned⟩ := supported
      · simp only [mem_support_pure_iff, reduceCtorEq] at returned
      · exact (mem_support_bind_iff _ _ _).2 ⟨reply, mem_support_query query reply, ih reply returned⟩

/-- Any stateful optional oracle interpreter preserves the original all-reply value support when it succeeds; its complete poststate is retained in the premise. -/
theorem interpreted_support {ι κ Result State : Type} {spec : OracleSpec.{0, 0} ι} {target : OracleSpec.{0, 0} κ}
    (impl : QueryImpl spec (OptionT (StateT State (OracleComp target))))
    (client : OracleComp spec Result) (before after : State) (value : Result)
    (supported : (some value, after) ∈ support (((simulateQ impl client).run).run before)) :
    value ∈ support client := by
  let handler : QueryImpl (RawCtxSelectedFamilyNonceCoupling.Optional spec) (StateT State (OracleComp target)) :=
    fun query => (impl query).run
  apply optional_support client value
  have equal := RawCtxSelectedFamilyNonceCoupling.optional_client
    (m := OracleComp target) (σ := State) (handler := impl) (client := client)
  rw [← equal] at supported
  apply support_simulateQ_run'_subset handler
    (RawCtxSelectedFamilyNonceCoupling.optionalClient client) before
  simpa only [StateT.run'_eq, support_map, Set.mem_image] using
    (show ∃ result ∈ support ((simulateQ handler (RawCtxSelectedFamilyNonceCoupling.optionalClient client)).run before), result.1 = some value from
      ⟨(some value, after), supported, rfl⟩)

open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhNativeSharedPrefix
open RawCtxSelectedParentTable RawCtxSelectedParentEntry PqxdhFirstRecordConfidentiality
variable {ι I D K X Response Shared A N C M P Result : Type} {extra : OracleSpec ι} {S B : Nat}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool) (monitor : Fin B)

/-- Executing the retained request selects one of its own outside programs, preserving every all-reply property of returned values. All record, finish and Builder effects remain in the actual supported preparation. -/
theorem prepare_returns (property : Result → Prop) (qPost : Nat)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Bool S B)
    (material : PqxdhOrderedChainHybrids.Material) (fits : PqxdhInitialOriginCertificates.Fits qPost context)
    (valid : PqxdhLaterSavedOutsideSupport.Returns property context) (localState : Local A N C)
    (result : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result × InsState M P I D K A N C S B)
    (supported : result ∈ support (PqxdhLaterSavedPostCompiler.prepare pre application initial selector aux source writer prior target
      nonce next sender read qPost context material fits localState)) :
    ∀ value, value ∈ support result.1 → property value := by
  rcases context with ⟨(record | finish) | builder, trace, origin⟩
  all_goals simp only [PqxdhLaterSavedPostCompiler.prepare, mem_support_bind_iff, mem_support_pure_iff] at supported
  case inr =>
    obtain ⟨sealed, _, published, _, rfl⟩ := supported
    exact valid _
  all_goals obtain ⟨reply, _, rfl⟩ := supported
  all_goals exact valid _

/-- The complete saved compiler preserves every all-reply property of the actual outside program when it returns a value. The complete instrumented state and refused executions remain in the program. -/
theorem complete_returns (property : Result → Prop) (qPost : Nat)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Bool S B)
    (material : PqxdhOrderedChainHybrids.Material) (fits : PqxdhInitialOriginCertificates.Fits qPost context)
    (valid : PqxdhLaterSavedOutsideSupport.Returns property context) (localState : Local A N C)
    (value : Result) (after : InsState M P I D K A N C S B)
    (supported : (some value, after) ∈ support (PqxdhLaterSavedPostCompiler.complete pre application initial selector aux source writer
      prior target nonce next mark sender route read monitor qPost context material fits localState)) :
    property value := by
  simp only [PqxdhLaterSavedPostCompiler.complete, mem_support_bind_iff] at supported
  obtain ⟨prepared, actual, returned⟩ := supported
  exact prepare_returns pre application initial selector aux source writer prior target nonce next sender read property qPost
    context material fits valid localState prepared actual value
    (interpreted_support _ prepared.1 prepared.2 after value returned)

/-- Completing the descriptor produced by an actual callback cut returns an all-reply value of that same callback. This applies directly to the executable compiler, without inventing a frame reply or reconstructing an interpreted prefix. -/
theorem source_support {State : Type}
    (selected : (PqxdhInitialPostContext.Base extra RatchetChain I D K X Response Shared S B).Domain → State → Bool)
    (selection : ∀ query state, selected query state = true → PqxdhInitialOriginForwardPost.selected query = true)
    (impl : QueryImpl (PqxdhInitialPostContext.Base extra RatchetChain I D K X Response Shared S B) (StateT State ProbComp))
    (client : OracleComp (PqxdhInitialPostContext.PostSpec extra S B) Result)
    (before : PqxdhInitialPostContext.NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Bool S B)
    (state reached : State) (qPost : Nat)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Bool S B)
    (cut : RawCtxForwardScan.Cut.pending context reached ∈ support
      (RawCtxForwardScan.scan PqxdhInitialOriginForwardPost.selected selected selection impl
        (PqxdhInitialOriginForwardPost.program mark sender route read client before trace)
        (PqxdhInitialOriginForwardPost.program_covered mark sender route read client before trace) state))
    (material : PqxdhOrderedChainHybrids.Material) (fits : PqxdhInitialOriginCertificates.Fits qPost context)
    (localState : Local A N C) (value : Result) (after : InsState M P I D K A N C S B)
    (completed : (some value, after) ∈ support (PqxdhLaterSavedPostCompiler.complete pre application initial selector aux source writer
      prior target nonce next mark sender route read monitor qPost context material fits localState)) :
    value ∈ support client :=
  complete_returns pre application initial selector aux source writer prior target nonce next sender route read mark monitor
    (fun result => result ∈ support client) qPost context material fits
    (PqxdhLaterSavedOutsideSupport.scan_returns (fun result => result ∈ support client) mark sender route read selected selection
      impl client (fun _ supported => supported) before trace state reached context cut) localState value after completed

end BeaconcryptCore.Computational.PqxdhLaterSavedCompilerSupport

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedCompilerSupport.optional_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedCompilerSupport.optional_support
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedCompilerSupport.interpreted_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedCompilerSupport.interpreted_support
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedCompilerSupport.prepare_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedCompilerSupport.prepare_returns
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedCompilerSupport.complete_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedCompilerSupport.complete_returns
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedCompilerSupport.source_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedCompilerSupport.source_support
