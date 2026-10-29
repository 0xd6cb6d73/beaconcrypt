-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessStep

/-! The actual initialized original Word ledger derives native preparation safety internally. The additive observer is followed through every supported adaptive continuation using the already proved live-Ready certificate, including the complete chronological trace. No injectivity, caller source equation or preparation premise is introduced in the initialized endpoint. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessRun
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (input)
open RegistrationNativeSecretWordInterface (Spec)
open RegistrationNativeSecretWordInterpreter (State Provider)
open RegistrationNativeSecretWordInterpreterChecked (handlerChecked AllPrepared Prefix)
open RegistrationNativeSecretWordNativeReadiness (Audit Good handler initial)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret)

/-- Actual supported adaptive execution preserves reflected native flags and has no unprepared valid native demand once the concrete Word preparation certificate is supplied. -/
theorem program_good (work : OracleComp (Spec n KemSK) Value) (before : Audit × State n KemSK)
    (good : Good setup seed scalar candidate before.1 before.2)
    (safe : AllPrepared (input setup.joint setup.dh seed scalar)
      (handlerChecked setup wire route sign (input setup.joint setup.dh seed scalar) inside provider) work before.2)
    (result : Value × (Audit × State n KemSK))
    (supported : result ∈ support ((simulateQ (handler setup wire route sign inside provider seed scalar candidate) work).run before)) :
    Good setup seed scalar candidate result.2.1 result.2.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact good
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨reached, called, continued⟩ := supported
      have baseCalled : (reached.1, reached.2.2) ∈ support
          ((handlerChecked setup wire route sign (input setup.joint setup.dh seed scalar) inside provider query).run before.2) := by
        have mapped := Set.mem_image_of_mem (Prod.map id Prod.snd) called
        rw [← support_map, RegistrationNativeSecretWordNativeReadiness.erase_query] at mapped
        exact mapped
      have afterGood := RegistrationNativeSecretWordNativeReadinessStep.query_good setup wire route sign inside provider seed scalar candidate
        query before good (safe query next before.2 (.refl _ _)) reached called
      apply ih reached.1 reached.2 afterGood ?_ result continued
      intro later tail after path
      exact safe later tail after (.step query next before.2 reached.1 reached.2.2 _ after baseCalled path)

/-- The complete initialized original ledger and chronology have no native unprepared-demand audit failure; their actual live-Ready certificate and cold flags are derived internally. -/
theorem initialized_trace (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (frontend : RegistrationNativeSecretWordMessage.State source) (empty : frontend.server.sessions = [])
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (kem : RegistrationNativeSecretWordKemProvider.State KemSK)
    (result : ((((Value × RegistrationNativeLedger.State) × RegistrationNativeSecretWordMessage.State source) ×
      RegistrationNativeSecretWordFrontendTrace.State) × (Audit × State n KemSK)))
    (supported : result ∈ support
      ((simulateQ (handler setup wire route sign inside provider seed scalar candidate)
        (RegistrationNativeSecretWordFrontendTrace.program
          (RegistrationNativeSecretWordFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey
            serverKeyId bounds mode work frontend))).run
        (initial, RegistrationNativeSecretWordInterpreter.initial ordinary kem))) :
    result.2.1.bad = false := by
  have safe := RegistrationNativeSecretWordLiveFrontendSource.traced_prepared setup checks wire source route sign
    (input setup.joint setup.dh seed scalar) inside provider selectedOwner selectedAccept publicPrekey serverKeyId
    bounds mode work frontend empty ordinary kem
  exact (program_good setup wire route sign inside provider seed scalar candidate _ _
    (RegistrationNativeSecretWordNativeReadiness.initial_good setup seed scalar candidate ordinary kem)
    safe result supported).2.2
end BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessRun
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessRun.program_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessRun.program_good
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessRun.initialized_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessRun.initialized_trace
