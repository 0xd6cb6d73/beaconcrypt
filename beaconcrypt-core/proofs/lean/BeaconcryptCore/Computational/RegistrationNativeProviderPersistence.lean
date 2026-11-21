-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderBuildFrame
import BeaconcryptCore.Computational.RegistrationNativeProviderSource
import BeaconcryptCore.Computational.RegistrationNativePublicSourcePersistence

/-! The actual provider source preserves every earlier prepared root. Provider calls may change their own state, the live KEM pool and shared World counters, but cannot inspect or overwrite the root memo. All other callbacks use the existing literal source semantics, including failed and repeated preparations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderPersistence
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeProviderInterpreter (Provider State handler)
open RegistrationNativeProviderSource (close)
open RegistrationNativePublicSourceState (MemoCorrect)
open RegistrationNativeProviderBuildCaps (IsRoutedKem)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

/-- Every actual source callback preserves source-correct roots and all earlier successful memo entries. -/
theorem query_stable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (before : State n KemSK ProviderState)
    (result : (RegistrationNativePublicFrontend.Spec n KemSK).Range query × State n KemSK ProviderState)
    (correct : MemoCorrect setup seed scalar before.1.roots)
    (supported : result ∈ support ((close setup seed scalar (handler setup wire route sign provider query)).run before)) :
    MemoCorrect setup seed scalar result.2.1.roots ∧
      ∀ message root, before.1.roots message = some root → result.2.1.roots message = some root := by
  by_cases routed : IsRoutedKem query
  · rcases query with (message | (query | query)) | query
    · exact routed.elim
    · exact routed.elim
    · change result ∈ support ((close setup seed scalar
        (RegistrationNativeProviderInterpreter.routed provider query)).run before) at supported
      rw [RegistrationNativeProviderSource.routed_source, support_map] at supported
      obtain ⟨inner, _possible, equal⟩ := supported
      cases equal
      exact ⟨correct, fun _ _ stored => stored⟩
    · exact routed.elim
  · rw [RegistrationNativeProviderBuildFrame.query_free setup wire route sign provider query routed,
      RegistrationNativeProviderSource.withBase_source, support_map] at supported
    obtain ⟨inner, reached, equal⟩ := supported
    have stable := RegistrationNativePublicSourcePersistence.query_stable setup wire route sign seed scalar query
      before.1 inner correct reached
    cases equal
    exact stable

/-- Entire adaptive reference-source programs preserve all earlier root receipts under the same arbitrary provider. -/
theorem program_stable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : State n KemSK ProviderState) (result : Value × State n KemSK ProviderState)
    (correct : MemoCorrect setup seed scalar before.1.roots)
    (supported : result ∈ support
      ((close setup seed scalar (simulateQ (handler setup wire route sign provider) work)).run before)) :
    MemoCorrect setup seed scalar result.2.1.roots ∧
      ∀ message root, before.1.roots message = some root → result.2.1.roots message = some root := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure output =>
      change result ∈ support (pure (output, before)) at supported
      rw [mem_support_pure_iff] at supported
      subst result
      exact ⟨correct, fun _ _ stored => stored⟩
  | query_bind query next ih =>
      have split : (close setup seed scalar (simulateQ (handler setup wire route sign provider)
          (((RegistrationNativePublicFrontend.Spec n KemSK).query query :
            OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) _) >>= next))).run before = (do
          let step ← (close setup seed scalar (handler setup wire route sign provider query)).run before
          (close setup seed scalar (simulateQ (handler setup wire route sign provider) (next step.1))).run step.2) := by
        simp only [close, simulateQ_bind, simulateQ_spec_query, StateT.run,
          StateT.monad_bind_def, StateT.bind, simulateQ_bind]
      rw [split, mem_support_bind_iff] at supported
      obtain ⟨step, reached, tail⟩ := supported
      obtain ⟨firstCorrect, firstKeeps⟩ := query_stable setup wire route sign seed scalar provider query before step correct reached
      obtain ⟨lastCorrect, lastKeeps⟩ := ih step.1 step.2 result firstCorrect tail
      exact ⟨lastCorrect, fun message root stored => lastKeeps message root (firstKeeps message root stored)⟩

end BeaconcryptCore.Computational.RegistrationNativeProviderPersistence

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderPersistence.query_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderPersistence.query_stable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderPersistence.program_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderPersistence.program_stable
