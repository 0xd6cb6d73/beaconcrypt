-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationRootStage
import BeaconcryptCore.Computational.RegistrationServerReferenceSourceClient

/-! Arbitrary concrete Server primitive state, including a KEM provider pool and phase, survives static-DH reference preparation. Only the private related-family instrumentation is projected; all local effects and the shared cache remain exact. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerProviderPrefix
open PqxdhJointIdentity (Primitives IdentitySeed PeerEncoding)
open PqxdhJointGapDh (DhInterface ScalarBytes)
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhServerRelatedRootConsumer (State)
variable {Auxiliary Result : Type}

/-- Each actual public-reference prefix query retains the full supplied primitive state after dropping only root-family instrumentation. -/
theorem prefix_step (joint : Primitives) (domain : PqxdhServerStaticDhSource.PublicDomain joint)
    (backend : QueryImpl RegistrationAgreementExecutor.Spec (StateT Auxiliary ProbComp))
    (visit : Word32 → StateT Auxiliary ProbComp Unit)
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit PeerEncoding).Domain)
    (before : State Auxiliary) :
    Prod.map id Prod.snd <$>
      (PqxdhServerStaticDhSource.prefixImpl domain
        (RegistrationAgreementInterpreter.prepImpl (RegistrationRootStage.lifted backend))
        (fun point => RegistrationRootStage.lift (visit point)) query).run before =
      (PqxdhServerStaticDhSource.prefixImpl domain (RegistrationAgreementInterpreter.prepImpl backend) visit query).run before.2 := by
  cases query with
  | decode raw =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        RegistrationRootStage.prep_project backend (.decode raw) before
  | identity packet =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        RegistrationRootStage.prep_project backend (.identity packet) before
  | identityPoint key =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        RegistrationRootStage.prep_project backend (.identityPoint key) before
  | pqField packet =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        RegistrationRootStage.prep_project backend (.pqField packet) before
  | preField packet =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        RegistrationRootStage.prep_project backend (.preField packet) before
  | oneField packet =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        RegistrationRootStage.prep_project backend (.oneField packet) before
  | verify key signed =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        RegistrationRootStage.prep_project backend (.verify key signed) before
  | registrationStatus rid =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        RegistrationRootStage.prep_project backend (.registrationStatus rid) before
  | reserveRegistration =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        RegistrationRootStage.prep_project backend (.reserveRegistration) before
  | parseDh point =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        RegistrationRootStage.prep_project backend (.parseDh point) before
  | generate =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        RegistrationRootStage.prep_project backend (.generate) before
  | parseKem key =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        RegistrationRootStage.prep_project backend (.parseKem key) before
  | encapsulate key =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        RegistrationRootStage.prep_project backend (.encapsulate key) before
  | publicConversion key =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        RegistrationRootStage.prep_project backend (.publicConversion key) before
  | privateConversion =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        RegistrationRootStage.prep_project backend (.privateConversion) before
  | ephemeralDh secret key =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        RegistrationRootStage.prep_project backend (.ephemeralDh secret key) before
  | staticDh point =>
      change Prod.map id Prod.snd <$> (do
        let visited ← (RegistrationRootStage.lift (visit point)).run before
        pure (PqxdhServerStaticDhSource.selectedReply domain point, visited.2)) =
        (do let visited ← (visit point).run before.2
            pure (PqxdhServerStaticDhSource.selectedReply domain point, visited.2))
      simp only [RegistrationRootStage.lift, StateT.run, bind_map_left, map_bind, map_pure, Prod.map_def, id_eq]

/-- The whole actual collector has exactly the same current auxiliary state, cache and optional failure result. -/
theorem prefix_program (joint : Primitives) (domain : PqxdhServerStaticDhSource.PublicDomain joint)
    (backend : QueryImpl RegistrationAgreementExecutor.Spec (StateT Auxiliary ProbComp))
    (visit : Word32 → StateT Auxiliary ProbComp Unit)
    (work : OracleComp (PqxdhServerRootPreparation.Spec registration.InitPacket Unit PeerEncoding) Result)
    (before : State Auxiliary) :
    Prod.map id Prod.snd <$>
      (simulateQ (PqxdhServerStaticDhSource.prefixImpl domain
        (RegistrationAgreementInterpreter.prepImpl (RegistrationRootStage.lifted backend))
        (fun point => RegistrationRootStage.lift (visit point))) work).run before =
      (simulateQ (PqxdhServerStaticDhSource.prefixImpl domain (RegistrationAgreementInterpreter.prepImpl backend) visit) work).run before.2 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.snd (prefix_step joint domain backend visit) work before

/-- Source root completion preserves the entire supplied local state while only the private family history/cache is discarded. -/
theorem consumer_program (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect source hmac) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (work : OracleComp PqxdhServerRelatedRootConsumer.Spec Result)
    (before : State Auxiliary) :
    Prod.map id Prod.snd <$>
      (simulateQ (PqxdhServerRelatedRootConsumer.impl
        (RegistrationServerRootCompiler.family hmac joint dh seed scalar) RegistrationAgreementFinish.quiet) work).run before =
      (fun value => (value, before.2)) <$>
        simulateQ (RegistrationServerReferenceSourceClient.consumer source hmac joint dh seed scalar) work := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      cases query with
      | inl query =>
          simp only [PqxdhServerRelatedRootConsumer.impl, PqxdhServerRelatedRootConsumer.familyImpl, StateT.run, bind_map_left]
          have value := RegistrationNativeSourceRoot.legacy_query source hmac correct joint dh seed scalar query before.1
          have head := congrArg (fun distribution => distribution >>= fun reply =>
            (fun value => (value, before.2)) <$> simulateQ
              (RegistrationServerReferenceSourceClient.consumer source hmac joint dh seed scalar) (next reply)) value
          simp only [bind_map_left] at head
          calc
            _ = (RegistrationServerRootCompiler.family hmac joint dh seed scalar query).run before.1 >>= fun result =>
                (fun value => (value, before.2)) <$> simulateQ
                  (RegistrationServerReferenceSourceClient.consumer source hmac joint dh seed scalar) (next result.1) := by
              apply bind_congr
              rintro ⟨reply, after⟩
              simpa only [StateT.run] using ih reply (after, before.2)
            _ = _ := by
              rw [head]
              simp only [RegistrationServerReferenceSourceClient.consumer, ]
      | inr query =>
          simp only [PqxdhServerRelatedRootConsumer.impl, pure_bind,
            RegistrationServerReferenceSourceClient.consumer, ]
          exact ih () before

end BeaconcryptCore.Computational.RegistrationServerProviderPrefix
/-- info: 'BeaconcryptCore.Computational.RegistrationServerProviderPrefix.prefix_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerProviderPrefix.prefix_step
/-- info: 'BeaconcryptCore.Computational.RegistrationServerProviderPrefix.prefix_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerProviderPrefix.prefix_program
/-- info: 'BeaconcryptCore.Computational.RegistrationServerProviderPrefix.consumer_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerProviderPrefix.consumer_program
