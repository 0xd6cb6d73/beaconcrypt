-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServer
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveRootEcho

/-! A successful native Word agreement exposes its own supported collector and checked root-client continuation. The retained reference equals the descriptor computed by that very collector; no unrelated preparation witness can be used for target provenance. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerOrigin
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message ServerReady)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordLiveServerRun (State Auxiliary close lower)
open RegistrationNativeSecretWordLiveServer (implementation)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (selected : Bool)

/-- The actual successful Server agreement retains its own complete collector and root continuation, with exact descriptor echo. -/
theorem agreement (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before after : State n KemSK) (ready : ServerReady)
    (supported : (.ok (some ready), after) ∈ support
      ((close (implementation setup wire route sign input inside provider selected)
        (RegistrationNativeSecretWordServerCompiler.agreement setup checks packet authenticated)).run before)) :
    ∃ collected middle,
      (some collected, middle) ∈ support
        ((lower (implementation setup wire route sign input inside provider selected)
          (RegistrationNativeSecretWordServerCompiler.collect setup checks packet authenticated)).run before.2) ∧
      (.ok (some ready), after.2.2) ∈ support
        ((simulateQ (RegistrationNativeSecretWordLiveRoot.preparation setup wire route sign input inside provider)
          (RegistrationNativeSecretWordServerRoot.client authenticated.binding collected)).run middle.2) ∧
      ready.reference = RegistrationNativeSecretWordServerRoot.message collected := by
  rw [RegistrationNativeSecretWordLiveServerRun.agreement_run, mem_support_bind_iff] at supported
  obtain ⟨collected, called, supported⟩ := supported
  cases formed : collected.1 with
  | none => simp only [formed, mem_support_pure_iff] at supported; cases supported
  | some pending =>
      simp only [formed, support_map] at supported
      obtain ⟨reached, possible, equal⟩ := supported
      have pairEqual : reached = (.ok (some ready), after.2.2) :=
        Prod.ext (congrArg (fun result => result.1) equal) (congrArg (fun result => result.2.2.2) equal)
      have same : (simulateQ (implementation setup wire route sign input inside provider selected)
          (simulateQ RegistrationNativeSecretWordInterface.prepare
            (RegistrationNativeSecretWordServerRoot.client authenticated.binding pending))).run collected.2.2 =
          (simulateQ (RegistrationNativeSecretWordLiveRoot.preparation setup wire route sign input inside provider)
            (RegistrationNativeSecretWordServerRoot.client authenticated.binding pending)).run collected.2.2 := by
        rw [← QueryImpl.simulateQ_compose]
        congr 2
      rw [same, pairEqual] at possible
      refine ⟨pending, collected.2, ?_, possible, ?_⟩
      · simpa only [← formed, Prod.mk.eta] using called
      · exact RegistrationNativeSecretWordLiveRootEcho.server setup wire route sign input inside provider authenticated.binding pending ready collected.2.2 after.2.2 possible

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerOrigin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerOrigin.agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerOrigin.agreement
