-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveCaps
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendTrace

/-! The chronological private trace forwards every actual query once. Preparation safety therefore lifts through the complete trace observer while retaining both the reached protocol state and every recorded failed or successful callback. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveTrace
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterface (Spec)
open RegistrationNativeSecretWordInterpreter (Provider State)
open RegistrationNativeSecretWordInterpreterChecked (handlerChecked AllPrepared)
open RegistrationNativeSecretWordLiveFlags (Valid)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

private theorem state_bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (state : S) :
    (work >>= next) state = (do let result ← work state; next result.1 result.2) := rfl

/-- A derived actual preparation certificate survives the complete chronological observer without changing any reached service state. -/
theorem program (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (work : OracleComp (Spec n KemSK) Value) (before : State n KemSK)
    (observed : RegistrationNativeSecretWordFrontendTrace.State) (valid : Valid input before)
    (safe : AllPrepared input (handlerChecked setup wire route sign input inside provider) work before) :
    AllPrepared input (handlerChecked setup wire route sign input inside provider)
      ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler work).run observed) before := by
  induction work using OracleComp.inductionOn generalizing before observed with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure]
      exact RegistrationNativeSecretWordLiveCaps.no_demand setup wire route sign input inside provider _ before valid (by trivial)
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run, state_bind_apply,
        RegistrationNativeSecretWordFrontendTrace.handler, bind_map_left]
      apply RegistrationNativeSecretWordLivePrefix.query input (handlerChecked setup wire route sign input inside provider) query _ before
      · exact safe query next before (.refl _ _)
      · intro result supported
        have flags := RegistrationNativeSecretWordLiveFlags.query_receipts setup wire route sign input inside provider query before valid result supported
        apply ih result.1 result.2 _ flags.1
        intro later tail after path
        exact safe later tail after (.step query next before result.1 result.2 _ after supported path)

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveTrace
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveTrace.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveTrace.program
