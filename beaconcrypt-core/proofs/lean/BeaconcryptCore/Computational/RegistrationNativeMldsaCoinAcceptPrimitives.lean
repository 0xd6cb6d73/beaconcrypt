-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaCoinPrimitives
import BeaconcryptCore.Computational.RegistrationAuthenticationBounds
import BeaconcryptCore.Computational.RegistrationNativeAcceptCosts
import BeaconcryptCore.Computational.RegistrationNativeMldsaCoinAgreementSyntax

/-! The actual Server accept source uses its original authentication and nine-step agreement controllers. Uniform costs are derived from their literal query syntax. The only supplied primitive cost is actual ML-KEM encapsulation; Server conversion, DH, rejected decapsulation and fixed source root HKDF remain deterministic. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaCoinAcceptPrimitives
attribute [local irreducible] RegistrationAuthenticationExecutor.execute registration.begin_init_authentication
open PqxdhServerAuthExperiment (Setup Codec Checks)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

private theorem simulated {Query State Result : Type} {queries : OracleSpec Query}
    (implementation : QueryImpl queries (StateT State ProbComp)) (slotCost : Nat)
    (step : ∀ query before, ((implementation query).run before).IsTotalQueryBound slotCost)
    (work : OracleComp queries Result) (cap : Nat) (bounded : work.IsTotalQueryBound cap) (before : State) :
    ((simulateQ implementation work).run before).IsTotalQueryBound (cap * slotCost) := by
  induction work using OracleComp.inductionOn generalizing cap before with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isTotalQueryBound_query_bind_iff] at bounded
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      apply (isTotalQueryBound_bind (step query before) (fun result => ih result.1 _ (bounded.2 result.1) result.2)).mono
      have positive : 1 ≤ cap := bounded.1
      calc
        slotCost + (cap - 1) * slotCost = (cap - 1) * slotCost + slotCost := Nat.add_comm _ _
        _ = (cap - 1 + 1) * slotCost := by rw [Nat.add_mul, Nat.one_mul]
        _ = cap * slotCost := by rw [Nat.sub_add_cancel positive]
        _ ≤ cap * slotCost := le_rfl

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (state : S) : (pure value : StateT S m X) state = pure (value, state) := rfl

private theorem authentication_query (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (query : RegistrationAuthenticationExecutor.Spec.Domain) (before : PqxdhRecordLiftWorld.State n) :
    ((RegistrationWorldAuthentication.implementation setup codec route verify query).run before).IsTotalQueryBound 64 := by
  cases query with
  | hash request =>
      simp only [RegistrationWorldAuthentication.implementation, QueryImpl.apply_compose,
        RegistrationWorldAuthentication.callbacks, bind_pure_comp, simulateQ_map, simulateQ_spec_query,
        PqxdhRecordLiftWorld.handler, StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff]
      exact RegistrationNativeMldsaCoinPrimitives.hash _ before
  | mldsa request | ed25519 request => trivial

/-- All actual Init authentication outcomes pay at most eight source slots of64 uniform draws. -/
theorem authentication (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) (before : PqxdhRecordLiftWorld.State n) :
    ((RegistrationWorldAuthentication.begin setup codec route verify pin packet).run before).IsTotalQueryBound 512 := by
  unfold RegistrationWorldAuthentication.begin RegistrationWorldAuthentication.program
  rw [← QueryImpl.simulateQ_compose]
  change ((simulateQ (RegistrationWorldAuthentication.implementation setup codec route verify)
    (RegistrationAuthenticationExecutor.begin pin packet)).run before).IsTotalQueryBound 512
  exact simulated (RegistrationWorldAuthentication.implementation setup codec route verify) 64
    (authentication_query setup codec route verify) (RegistrationAuthenticationExecutor.begin pin packet)
      8 (RegistrationAuthenticationBounds.begin_bound pin packet) before

private theorem agreement_query (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (seed : PqxdhJointIdentity.IdentitySeed)
    (qEncap : Nat) (encapsulation : ∀ key, (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
      (setup.kem.encaps key)).IsTotalQueryBound qEncap)
    (query : RegistrationAgreementExecutor.Request) (before : RegistrationServerRoleBackend.State) :
    ((RegistrationAgreementShared.auxiliary setup.source
      (RegistrationServerRoleBackend.native setup checks representation seed) query).run before).IsTotalQueryBound (32 + qEncap) := by
  cases query with
  | convertPublic key => trivial
  | convertSecret role => cases role <;> trivial
  | generate role =>
      exact (RegistrationNativeAcceptCosts.ordinary_coins setup checks (.generate role) trivial before).mono (Nat.le_add_right 32 qEncap)
  | encapsulate key =>
      cases key with
      | none => trivial
      | some key =>
          simp only [RegistrationAgreementShared.auxiliary, RegistrationServerRoleBackend.native,
            RegistrationServerRoleBackend.localBackend]
          split
          · simp only [PqxdhServerAuthExperiment.encapsulate, simulateQ_map, StateT.run_lift,
              bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
            exact (encapsulation (RegistrationRootInput.pqKey key)).mono (Nat.le_add_left qEncap 32)
          · trivial
  | decapsulate ciphertext => trivial
  | dh request =>
      cases role : request.secret_role <;>
        simp only [RegistrationAgreementShared.auxiliary, RegistrationServerRoleBackend.native, role,
          RegistrationServerRoleBackend.localBackend, StateT.run, state_pure_apply, IsTotalQueryBound,
          isQueryBound_pure]
  | root request => trivial

private theorem agreement_continue {Input : Type} (action : RustM Input)
    (next : Input → OracleComp RegistrationAgreementExecutor.Spec (RustM agreement.AgreementEffect))
    (count : Nat) (bounded : ∀ value, (next value).IsTotalQueryBound count) :
    (RegistrationAgreementExecutor.continueWith action next).IsTotalQueryBound count := by
  cases action with
  | ok value => exact bounded value
  | fail error | div => trivial

private theorem replay_bound (control : pqxdh.ServerState) (authenticated : registration.AuthenticatedInit)
    (history : RegistrationReplaySchedule.State) :
    (RegistrationReplaySchedule.begin control authenticated history).IsTotalQueryBound 9 := by
  unfold RegistrationReplaySchedule.begin
  apply agreement_continue
  intro lookup
  apply agreement_continue
  intro requested
  apply agreement_continue
  intro effect
  exact RegistrationNativeMldsaCoinAgreementSyntax.drive 9 effect

private theorem world_agreement_query (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (seed : PqxdhJointIdentity.IdentitySeed)
    (qEncap : Nat) (encapsulation : ∀ key, (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
      (setup.kem.encaps key)).IsTotalQueryBound qEncap)
    (query : RegistrationAgreementExecutor.Request) (before : RegistrationServerRootCompiler.Local n) :
    ((RegistrationWorldAgreement.agreement setup.source (RegistrationServerRoleBackend.native setup checks representation seed) query).run before).IsTotalQueryBound
      (32 + qEncap) := by
  simpa only [RegistrationWorldAgreement.agreement, StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using
    RegistrationNativeMldsaCoinPrimitives.sampled _ (32 + qEncap)
      (agreement_query setup checks representation seed qEncap encapsulation query before.auxiliary) before.world.1

/-- Actual source replay lookup and agreement run nine fuel steps, each with at most32 scalar draws plus the declared encapsulation cap. -/
theorem agreement_bound (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (qEncap : Nat) (encapsulation : ∀ key, (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
      (setup.kem.encaps key)).IsTotalQueryBound qEncap)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationServerFrontendCompiler.State n) :
    ((RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run before).IsTotalQueryBound
      (9 * (32 + qEncap)) := by
  simpa only [RegistrationServerNativeSource.agree, StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using
    simulated (RegistrationWorldAgreement.agreement setup.source (RegistrationServerRoleBackend.native setup checks representation created.seed))
      (32 + qEncap) (world_agreement_query setup checks representation created.seed qEncap encapsulation)
      (RegistrationReplaySchedule.begin before.control authenticated before.consumed) 9
      (replay_bound before.control authenticated before.consumed) before.world
end BeaconcryptCore.Computational.RegistrationNativeMldsaCoinAcceptPrimitives

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinAcceptPrimitives.authentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinAcceptPrimitives.authentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinAcceptPrimitives.agreement_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinAcceptPrimitives.agreement_bound
