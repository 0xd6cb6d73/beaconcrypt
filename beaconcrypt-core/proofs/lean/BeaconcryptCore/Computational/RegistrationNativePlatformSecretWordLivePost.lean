-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveOpen
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveBuild
/-! Every literal corrected Word callback preserves the preparation validity and live retained Server references. Common platform effects remain part of the same checked execution; the source controllers derive their own retention and take receipts. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLivePost
attribute [local irreducible] RegistrationNativePlatformSecretWordOpen.accept
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordInterpreterChecked (handlerChecked)
open RegistrationNativeSecretWordLiveSessions (Live)
open RegistrationNativePlatformSecretWordOrdinary (State)
open RegistrationNativePlatformSecretWordLiveState (Good)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
local notation "impl" => handlerChecked setup wire route sign input inside provider

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map _ _ _

private theorem server_open {source : RegistrationNativeMldsa.Source}
    (work : RegistrationNativePlatformSecretWordLiveOpenRun.Work n KemSK Platform A)
    (before : State source Platform) (context : RegistrationNativeSecretWordInterpreter.State n KemSK)
    (post : ∀ reached ∈ support ((RegistrationNativePlatformSecretWordLiveOpenRun.close impl work).run
      (before.1.server, (before.1.environment, (before.2, context)))), Live reached.2.1 reached.2.2.2.2.flags)
    (result : (A × State source Platform) × RegistrationNativeSecretWordInterpreter.State n KemSK)
    (supported : result ∈ support ((simulateQ impl
      ((RegistrationNativePlatformSecretWordFrontend.serverOpen work).run before)).run context)) :
    Live result.1.2.1.server result.2.flags := by
  simp only [RegistrationNativePlatformSecretWordFrontend.serverOpen, StateT.run,
    simulateQ_map, map_apply, support_map] at supported
  obtain ⟨reached, possible, equal⟩ := supported
  have actual : (reached.1.1.1.1, (reached.1.1.1.2, (reached.1.1.2, (reached.1.2, reached.2)))) ∈ support
      ((RegistrationNativePlatformSecretWordLiveOpenRun.close impl work).run
        (before.1.server, (before.1.environment, (before.2, context)))) := by
    simp only [RegistrationNativePlatformSecretWordLiveOpenRun.close, StateT.run, support_map]
    exact ⟨reached, possible, rfl⟩
  have kept := post _ actual
  cases equal
  exact kept

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "typed" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer

/-- The actual corrected typed callback preserves valid preparation flags and every still-live retained capability. -/
theorem query (current : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State source Platform) (context : RegistrationNativeSecretWordInterpreter.State n KemSK)
    (good : Good input before context)
    (result : (RegistrationNativeRawAdapter.TypedSpec.Range current × State source Platform) × RegistrationNativeSecretWordInterpreter.State n KemSK)
    (supported : result ∈ support ((simulateQ impl ((typed current).run before)).run context)) :
    Good input result.1.2 result.2 := by
  have flags := RegistrationNativeSecretWordLiveFlags.program_receipts setup wire route sign input inside provider
    ((typed current).run before) context good.1 result supported
  refine ⟨flags.1, ?_⟩
  by_cases accepting : RegistrationNativeRawAdapter.kind current = 3
  · cases current with
    | inl coin => cases accepting
    | inr command =>
      cases command <;> simp [RegistrationNativeRawAdapter.kind] at accepting
      case accept packet =>
        simp only [RegistrationNativePlatformSecretWordFrontend.handler, RegistrationNativePlatformSecretWordFrontend.accept,
          StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind] at supported
        apply server_open setup wire route sign input inside provider _ _ context ?_ result supported
        intro reached called
        exact RegistrationNativePlatformSecretWordLiveOpen.accept setup wire route sign input inside provider _
          (RegistrationNativePlatformSecretWordOrdinary.platform reserveRegistration) checks source.verify packet _ reached good.1 good.2 called
  · by_cases building : RegistrationNativeRawAdapter.kind current = 4
    · cases current with
      | inl coin => cases building
      | inr command =>
        cases command <;> simp [RegistrationNativeRawAdapter.kind] at building
        case build handle application =>
          have raw : result.1 ∈ support ((typed (.inr (.build handle application))).run before) := by
            apply OracleComp.support_simulateQ_run'_subset impl _ context
            rw [StateT.run'_eq, support_map]
            exact Set.mem_image_of_mem Prod.fst supported
          have same := RegistrationNativePlatformSecretWordLiveBuild.sessions setup sign view failure allocation erased helper writer reservePeer
            source handle application before result.1 raw
          intro ready member
          rw [same] at member
          exact flags.2 ready.reference
            ((RegistrationNativeSecretWordLiveSessions.take_live handle before.1.server context.flags good.2).1 ready member)
    · have raw : result.1 ∈ support ((typed current).run before) := by
        apply OracleComp.support_simulateQ_run'_subset impl _ context
        rw [StateT.run'_eq, support_map]
        exact Set.mem_image_of_mem Prod.fst supported
      have same := RegistrationNativePlatformSecretWordLiveState.quiet_server setup checks wire source sign selectedOwner selectedAccept publicPrekey
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer current ⟨accepting, building⟩ before result.1 raw
      rw [same]
      exact RegistrationNativeSecretWordLiveSessions.mono _ _ _ flags.2 good.2

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLivePost

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLivePost.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLivePost.query
