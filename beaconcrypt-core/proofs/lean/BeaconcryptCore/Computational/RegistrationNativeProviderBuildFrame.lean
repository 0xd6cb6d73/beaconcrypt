-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderBuildCaps

/-! A concrete zero-provider-query certificate makes the complete actual build independent of the KEM provider. The full World, opaque pool, roots, receipts and extra provider state remain in the outcome. This is an AST theorem before any source restoration or metric projection. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderBuildFrame
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeProviderInterpreter (Provider State withBase)
open RegistrationNativeProviderBuildCaps (IsRoutedKem)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

theorem query_free (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (provider : Provider KemSK ProviderState) (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (quiet : ¬IsRoutedKem query) :
    RegistrationNativeProviderInterpreter.handler setup wire route sign provider query =
      withBase (RegistrationNativePublicInterpreter.handler setup wire route sign query) := by
  rcases query with (message | (query | query)) | query
  · rfl
  · rfl
  · exact False.elim (quiet trivial)
  · rfl

theorem program_free (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (provider : Provider KemSK ProviderState) (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (bounded : work.IsQueryBoundP IsRoutedKem 0) :
    simulateQ (RegistrationNativeProviderInterpreter.handler setup wire route sign provider) work =
      simulateQ (fun query => withBase (RegistrationNativePublicInterpreter.handler setup wire route sign query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      have quiet : ¬IsRoutedKem query := bounded.1.resolve_right (Nat.not_lt_zero _)
      simp only [simulateQ_bind, simulateQ_spec_query]
      rw [query_free setup wire route sign provider query quiet]
      apply congrArg (fun continuation => withBase (RegistrationNativePublicInterpreter.handler setup wire route sign query) >>= continuation)
      funext reply
      exact ih reply (by simpa using bounded.2 reply)

/-- No new provider behavior is substituted into a build; it executes no provider query and retains that whole frame exactly. -/
theorem build_frame (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (provider : Provider KemSK ProviderState) (handle : Nat) (application : Option (Slice U8))
    {source : RegistrationNativeMldsa.Source} (frontend : RegistrationNativePublicFrontend.State source)
    (before : State n KemSK ProviderState) :
    (simulateQ (RegistrationNativeProviderInterpreter.handler setup wire route sign provider)
      ((RegistrationNativePublicFrontend.serverOpen false
        (RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application)).run frontend)).run before =
      (fun result => (result.1, (result.2, before.2))) <$>
        (simulateQ (RegistrationNativePublicInterpreter.handler setup wire route sign)
          ((RegistrationNativePublicFrontend.serverOpen false
            (RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application)).run frontend)).run before.1 := by
  rw [program_free setup wire route sign provider _
    (RegistrationNativeProviderBuildCaps.frontend_zero setup.source wire checks sign handle application frontend)]
  exact RegistrationNativeProviderInterpreter.withBase_program _ _ before

end BeaconcryptCore.Computational.RegistrationNativeProviderBuildFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBuildFrame.query_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBuildFrame.query_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBuildFrame.program_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBuildFrame.program_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBuildFrame.build_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBuildFrame.build_frame
