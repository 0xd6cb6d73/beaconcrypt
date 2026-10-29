-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendState

/-! The actual typed frontend establishes and preserves its private preparation invariant. Server accept derives newly retained references from reached preparation; build removes a moved reference. Every other concrete callback keeps the Server roster and transports prior flags through the same actual interpreter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendPost
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordInterpreterChecked (handlerChecked)
open RegistrationNativeSecretWordLiveFrontendState (Good)
open RegistrationNativeSecretWordLiveSessions (Live)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (state : S) :
    (observe <$> work) state = Prod.map observe id <$> work state := by
  change (work state >>= fun result => pure (observe result.1, result.2)) = _
  rw [bind_pure_comp]
  rfl

private theorem server {source : RegistrationNativeMldsa.Source} (selected : Bool)
    (work : RegistrationNativeSecretWordServerCompiler.M n KemSK Value)
    (before : RegistrationNativeSecretWordMessage.State source)
    (context : RegistrationNativeSecretWordInterpreter.State n KemSK)
    (post : ∀ result ∈ support ((RegistrationNativeSecretWordLiveServerRun.close
        (RegistrationNativeSecretWordLiveServer.implementation setup wire route sign input inside provider selected) work).run
      (before.server, before.environment, context)), Live result.2.1 result.2.2.2.flags)
    (result : (Value × RegistrationNativeSecretWordMessage.State source) × RegistrationNativeSecretWordInterpreter.State n KemSK)
    (supported : result ∈ support ((simulateQ (handlerChecked setup wire route sign input inside provider)
      ((RegistrationNativeSecretWordFrontend.serverOpen selected work).run before)).run context)) :
    Live result.1.2.server result.2.flags := by
  simp only [RegistrationNativeSecretWordFrontend.serverOpen, StateT.run, simulateQ_map, state_map_apply, support_map] at supported
  obtain ⟨reached, possible, equal⟩ := supported
  have actual : (reached.1.1.1, (reached.1.1.2, reached.1.2, reached.2)) ∈ support
      ((RegistrationNativeSecretWordLiveServerRun.close
        (RegistrationNativeSecretWordLiveServer.implementation setup wire route sign input inside provider selected) work).run
          (before.server, before.environment, context)) := by
    rw [RegistrationNativeSecretWordLiveServerRun.close_program,
      RegistrationNativeSecretWordLiveServer.implementation, QueryImpl.simulateQ_compose, support_map]
    exact Set.mem_image_of_mem _ possible
  have kept := post _ actual
  cases equal
  exact kept

attribute [local irreducible] RegistrationNativeSecretWordServerCompiler.accept RegistrationNativeSecretWordServerCompiler.build

/-- Every supported concrete typed callback retains valid preparation flags and all live Server capabilities. -/
theorem query (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (current : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeSecretWordMessage.State source)
    (context : RegistrationNativeSecretWordInterpreter.State n KemSK) (good : Good input before context)
    (result : (RegistrationNativeRawAdapter.TypedSpec.Range current × RegistrationNativeSecretWordMessage.State source) × RegistrationNativeSecretWordInterpreter.State n KemSK)
    (supported : result ∈ support ((simulateQ (handlerChecked setup wire route sign input inside provider)
      ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey current).run before)).run context)) :
    Good input result.1.2 result.2 := by
  have flags := RegistrationNativeSecretWordLiveFlags.program_receipts setup wire route sign input inside provider
    ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey current).run before)
    context good.1 result supported
  refine ⟨flags.1, ?_⟩
  by_cases accepting : RegistrationNativeRawAdapter.kind current = 3
  · cases current with
    | inl coin => cases accepting
    | inr command =>
      cases command <;> simp [RegistrationNativeRawAdapter.kind] at accepting
      case accept packet =>
        simp only [RegistrationNativeSecretWordFrontend.handler, StateT.run_bind, StateT.run_get,
          StateT.run_modify, pure_bind] at supported
        apply server setup wire route sign input inside provider _ _ _ context ?_ result supported
        intro reached called
        exact RegistrationNativeSecretWordLiveServer.accept setup wire route sign input inside provider _ checks source.verify packet _ reached good.1 good.2 called
  · by_cases building : RegistrationNativeRawAdapter.kind current = 4
    · cases current with
      | inl coin => cases building
      | inr command =>
        cases command <;> simp [RegistrationNativeRawAdapter.kind] at building
        case build handle application =>
          apply server setup wire route sign input inside provider false _ before context ?_ result supported
          intro reached called
          exact RegistrationNativeSecretWordLiveServer.build setup wire route sign input inside provider false checks handle application _ reached good.1 good.2 called
    · have raw : result.1 ∈ support
          ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey current).run before) := by
        apply OracleComp.support_simulateQ_run'_subset (handlerChecked setup wire route sign input inside provider) _ context
        rw [StateT.run'_eq, support_map]
        exact Set.mem_image_of_mem Prod.fst supported
      have same := RegistrationNativeSecretWordLiveFrontendState.quiet_server setup checks wire source sign
        selectedOwner selectedAccept publicPrekey current ⟨accepting, building⟩ before result.1 raw
      rw [same]
      exact RegistrationNativeSecretWordLiveSessions.mono _ _ _ flags.2 good.2

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendPost
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendPost.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendPost.query
