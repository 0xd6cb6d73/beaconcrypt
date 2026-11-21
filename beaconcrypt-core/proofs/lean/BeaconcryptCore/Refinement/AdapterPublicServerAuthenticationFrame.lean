-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationNative
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Actual authentication callbacks alter the shared hash cache and real counters while retaining the live Server object, private replay set and installed peer store. The frame is derived from literal World hash effects on every outcome, including authentication rejection. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationFrame
open BeaconcryptCore.Computational
variable {n : Nat} {I KemSK Reader Response Value : Type} {base : OracleSpec I}

theorem hash_server (bytes : Pqxdh.Bytes) (before after : PqxdhRecordLiftWorld.State n)
    (digest : CtxRomAuth.CtxDigest)
    (supported : (digest, after) ∈ support
      ((PqxdhRecordLiftWorld.effects (.inr (.hash bytes))).run before)) :
    after.server = before.server := by
  simp only [PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability,
    PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp, Functor.map_map, support_map] at supported
  obtain ⟨result, _called, returned⟩ := supported
  have same := congrArg Prod.snd returned
  cases same
  rfl

theorem query_server (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (query : RegistrationAuthenticationExecutor.Spec.Domain)
    (before after : PqxdhRecordLiftWorld.State n)
    (reply : RegistrationAuthenticationExecutor.Spec.Range query)
    (supported : (reply, after) ∈ support
      ((RegistrationWorldAuthentication.implementation setup codec route verify query).run before)) :
    after.server = before.server := by
  cases query with
  | hash request =>
    simp only [RegistrationWorldAuthentication.implementation, QueryImpl.apply_compose,
      RegistrationWorldAuthentication.callbacks, bind_pure_comp, simulateQ_map, simulateQ_spec_query,
      PqxdhRecordLiftWorld.handler, StateT.run_map, support_map] at supported
    obtain ⟨⟨digest, current⟩, called, returned⟩ := supported
    have same := congrArg Prod.snd returned
    cases same
    exact hash_server _ before after digest called
  | mldsa request | ed25519 request =>
    simp only [RegistrationWorldAuthentication.implementation, QueryImpl.apply_compose,
      RegistrationWorldAuthentication.callbacks, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
    cases supported.2
    rfl

theorem program_server (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (work : OracleComp RegistrationAuthenticationExecutor.Spec Value)
    (before after : PqxdhRecordLiftWorld.State n) (reply : Value)
    (supported : (reply, after) ∈ support
      ((simulateQ (RegistrationWorldAuthentication.implementation setup codec route verify) work).run before)) :
    after.server = before.server := by
  induction work using OracleComp.inductionOn generalizing before after with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
    cases supported.2
    rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨⟨answer, middle⟩, called, continued⟩ := supported
    exact (ih answer middle after continued).trans (query_server setup codec route verify query before middle answer called)

attribute [local irreducible] RegistrationAuthenticationExecutor.begin

theorem begin_server (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before after : PqxdhRecordLiftWorld.State n)
    (reply : RustM (List RegistrationAuthenticationFlow.Event × registration.InitAuthentication))
    (supported : (reply, after) ∈ support
      ((RegistrationWorldAuthentication.begin setup codec route verify pin packet).run before)) :
    after.server = before.server := by
  unfold RegistrationWorldAuthentication.begin RegistrationWorldAuthentication.program at supported
  rw [← QueryImpl.simulateQ_compose] at supported
  exact program_server setup codec route verify (RegistrationAuthenticationExecutor.begin pin packet) before after reply supported

end BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationFrame

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationFrame.hash_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationFrame.hash_server

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationFrame.query_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationFrame.query_server

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationFrame.program_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationFrame.program_server

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationFrame.begin_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationFrame.begin_server
