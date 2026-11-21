-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessTrace

/-! The extra preparation observer is exactly recoverable from the same retained final chronology, not merely equal after erasure. Literal state embedding proves this for every actual query and adaptive program before any probabilistic closure. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessTraceSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (input)
open RegistrationNativeSecretWordInterface (Spec)
open RegistrationNativeSecretWordInterpreter (Provider State)
open RegistrationNativeSecretWordInterpreterChecked (handlerChecked)
open RegistrationNativeSecretWordNativeReadiness (Audit)
open RegistrationNativeSecretWordNativeReadinessTrace (read)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret)

abbrev Base (n : Nat) (KemSK : Type) := RegistrationNativeSecretWordFrontendTrace.State × State n KemSK
abbrev Observed (n : Nat) (KemSK : Type) := RegistrationNativeSecretWordFrontendTrace.State × (Audit × State n KemSK)

def embed (before : Base n KemSK) : Observed n KemSK :=
  (before.1, (read setup seed scalar candidate before.1, before.2))

noncomputable def unobserved : QueryImpl (Spec n KemSK) (StateT (Base n KemSK) (OracleComp RegistrationNativeSecretWordService.Combined)) :=
  ((handlerChecked setup wire route sign (input setup.joint setup.dh seed scalar) inside provider).mapStateTBase
    RegistrationNativeSecretWordFrontendTrace.handler).flattenStateT

noncomputable def observed : QueryImpl (Spec n KemSK) (StateT (Observed n KemSK) (OracleComp RegistrationNativeSecretWordService.Combined)) :=
  ((RegistrationNativeSecretWordNativeReadiness.handler setup wire route sign inside provider seed scalar candidate).mapStateTBase
    RegistrationNativeSecretWordFrontendTrace.handler).flattenStateT

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (map : A → B) (work : StateT S m A) (before : S) :
    (map <$> work) before = Prod.map map id <$> work before := StateT.run_map map work before

private theorem flattened_apply {S T : Type}
    (outer : QueryImpl (Spec n KemSK) (StateT T (OracleComp RegistrationNativeSecretWordService.Combined)))
    (inner : QueryImpl (Spec n KemSK) (StateT S (OracleComp (Spec n KemSK))))
    (query : (Spec n KemSK).Domain) (before : S × T) :
    (outer.mapStateTBase inner).flattenStateT query before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ outer ((inner query).run before.1)).run before.2 := rfl

/-- Every actual joint traced callback recovers precisely the extra observer from that same reached trace. -/
theorem query_source (query : (Spec n KemSK).Domain) (before : Base n KemSK) :
    Prod.map id (embed setup seed scalar candidate) <$>
      (unobserved setup wire route sign inside provider seed scalar query).run before =
      (observed setup wire route sign inside provider seed scalar candidate query).run (embed setup seed scalar candidate before) := by
  simp only [unobserved, observed, flattened_apply,
    RegistrationNativeSecretWordFrontendTrace.handler, StateT.run, simulateQ_map, simulateQ_spec_query,
    RegistrationNativeSecretWordNativeReadiness.handler, state_map_apply, Functor.map_map,
    Prod.map_def, id_eq, embed, RegistrationNativeSecretWordNativeReadinessTrace.query_read]

/-- The entire actual traced computation reconstructs the extra observer from its literal same-run chronology while retaining every original output and state. -/
theorem program_source (work : OracleComp (Spec n KemSK) Value) (before : Base n KemSK) :
    Prod.map id (embed setup seed scalar candidate) <$>
      (simulateQ (unobserved setup wire route sign inside provider seed scalar) work).run before =
      (simulateQ (observed setup wire route sign inside provider seed scalar candidate) work).run (embed setup seed scalar candidate before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (embed setup seed scalar candidate)
    (query_source setup wire route sign inside provider seed scalar candidate) work before
/-- The exact nested interpreter reconstructs the additive native observer from the same final retained chronological state. -/
theorem nested_source (work : OracleComp (Spec n KemSK) Value)
    (trace : RegistrationNativeSecretWordFrontendTrace.State) (before : State n KemSK) :
    (simulateQ (RegistrationNativeSecretWordNativeReadiness.handler setup wire route sign inside provider seed scalar candidate)
      ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler work).run trace)).run
        (read setup seed scalar candidate trace, before) =
      (fun result => (result.1, (read setup seed scalar candidate result.1.2, result.2))) <$>
        (simulateQ (handlerChecked setup wire route sign (input setup.joint setup.dh seed scalar) inside provider)
          ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler work).run trace)).run before := by
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT,
    OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  change (fun result : Value × Observed n KemSK => ((result.1, result.2.1), result.2.2)) <$>
      (simulateQ (observed setup wire route sign inside provider seed scalar candidate) work).run
        (embed setup seed scalar candidate (trace, before)) = _
  rw [← program_source]
  simp only [Functor.map_map, Prod.map_def, id_eq, embed, unobserved]

/-- The final trace of the actual initialized checked frontend has no valid native demand without preparation, with no caller preparation or source premise. -/
theorem initialized_no_bad (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (frontend : RegistrationNativeSecretWordMessage.State source) (empty : frontend.server.sessions = [])
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (kem : RegistrationNativeSecretWordKemProvider.State KemSK)
    (result : ((((Value × RegistrationNativeLedger.State) × RegistrationNativeSecretWordMessage.State source) ×
      RegistrationNativeSecretWordFrontendTrace.State) × State n KemSK))
    (supported : result ∈ support
      ((simulateQ (handlerChecked setup wire route sign (input setup.joint setup.dh seed scalar) inside provider)
        (RegistrationNativeSecretWordFrontendTrace.program
          (RegistrationNativeSecretWordFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey
            serverKeyId bounds mode work frontend))).run (RegistrationNativeSecretWordInterpreter.initial ordinary kem))) :
    (read setup seed scalar candidate result.1.2).bad = false := by
  have mapped := Set.mem_image_of_mem
    (fun actual => (actual.1, (read setup seed scalar candidate actual.1.2, actual.2))) supported
  rw [← support_map] at mapped
  have observed := nested_source setup wire route sign inside provider seed scalar candidate
    (RegistrationNativeSecretWordFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work frontend)
    RegistrationNativeSecretWordFrontendTrace.initial (RegistrationNativeSecretWordInterpreter.initial ordinary kem)
  simp only [RegistrationNativeSecretWordFrontendTrace.program] at mapped
  rw [← observed] at mapped
  exact RegistrationNativeSecretWordNativeReadinessRun.initialized_trace setup wire route sign inside provider seed scalar candidate
    checks source selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work frontend empty ordinary kem
    (result.1, (read setup seed scalar candidate result.1.2, result.2)) mapped

end BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessTraceSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessTraceSource.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessTraceSource.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessTraceSource.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessTraceSource.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessTraceSource.nested_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessTraceSource.nested_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessTraceSource.initialized_no_bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessTraceSource.initialized_no_bad
