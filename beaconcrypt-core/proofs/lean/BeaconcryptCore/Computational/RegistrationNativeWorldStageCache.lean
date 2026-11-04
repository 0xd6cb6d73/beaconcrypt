-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaServerCached

/-! Actual first-record and publication source cuts retain their precise shared-cache extension and unchanged signing prefix on every failure and success. These facts keep intermediate source states connected to the final native cache. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeWorldStageCache
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationWorldAgreement (State)
variable {n : Nat} {ι KemSK Auxiliary Value Next Reader Response Encoded : Type} {base : OracleSpec ι}
attribute [local irreducible] RegistrationServerNativeSource.authenticate RegistrationWorldAuthentication.begin RegistrationAuthenticationShared.begin
  RegistrationWorldAuthentication.program RegistrationAuthenticationExecutor.execute registration.begin_init_authentication
private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (state : S) : (pure value : StateT S m X) state = pure (value, state) := rfl

variable {anchor : CtxRomAuth.CtxRO.QueryCache}

private def Valid (before : State n Auxiliary) : Prop := anchor ≤ before.world.1.primitive.2
private def Keeps (work : StateT (State n Auxiliary) ProbComp Value) : Prop :=
  ∀ before, Valid (anchor := anchor) before → ∀ result, result ∈ support (work.run before) → Valid (anchor := anchor) result.2

private theorem pure_keeps (value : Value) : Keeps (anchor := anchor) (pure value : StateT (State n Auxiliary) ProbComp Value) := by
  intro before valid result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact valid
private theorem bind_keeps (work : StateT (State n Auxiliary) ProbComp Value)
    (next : Value → StateT (State n Auxiliary) ProbComp Next) (first : Keeps (anchor := anchor) work)
    (rest : ∀ value, Keeps (anchor := anchor) (next value)) : Keeps (anchor := anchor) (work >>= next) := by
  intro before valid result supported
  rw [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact rest middle.1 middle.2 (first before valid middle reached) result continued

private theorem shared_facts (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : MldsaSharedNative.Spec.Domain) (before : State n Auxiliary)
    (result : MldsaSharedNative.Spec.Range query × State n Auxiliary)
    (supported : result ∈ support ((RegistrationWorldRecords.shared setup codec query).run before)) :
    before.world.1.primitive.2 ≤ result.2.world.1.primitive.2 ∧ result.2.world.2 = before.world.2 := by
  cases query with
  | inl query =>
      simp only [RegistrationWorldRecords.shared, StateT.run, support_map] at supported
      obtain ⟨inner, possible, same⟩ := supported
      cases same
      exact ⟨RegistrationWorldCache.effects_cache _ before.world.1 inner possible, rfl⟩
  | inr query =>
      simp only [RegistrationWorldRecords.shared, RegistrationWorldRecords.record, StateT.run, support_map] at supported
      obtain ⟨inner, possible, same⟩ := supported
      cases same
      exact ⟨RegistrationWorldCache.primitive_cache setup codec query before.world.1.primitive inner possible, rfl⟩

private theorem shared_program_facts (setup : Setup base KemSK) (codec : Codec Reader Response)
    (work : OracleComp MldsaSharedNative.Spec Value) (before : State n Auxiliary)
    (result : Value × State n Auxiliary)
    (supported : result ∈ support ((simulateQ (RegistrationWorldRecords.shared setup codec) work).run before)) :
    before.world.1.primitive.2 ≤ result.2.world.1.primitive.2 ∧ result.2.world.2 = before.world.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact ⟨le_refl _, rfl⟩
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, continued⟩ := supported
      obtain ⟨cached, receipts⟩ := shared_facts setup codec query before middle reached
      obtain ⟨laterCache, laterReceipts⟩ := ih middle.1 middle.2 result continued
      exact ⟨cached.trans laterCache, laterReceipts.trans receipts⟩

private theorem records_query_keeps (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RegistrationRecordPrimitives.Spec.Domain) : Keeps (anchor := anchor) (RegistrationWorldRecords.handler (n := n) (Auxiliary := Auxiliary) setup codec query) := by
  intro before valid result supported
  simp only [RegistrationWorldRecords.handler, StateT.run, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  obtain ⟨cached, _receipts⟩ := shared_program_facts setup codec (RegistrationRecordPrimitives.callbacks setup.source query) before inner possible
  exact valid.trans cached

private theorem records_keeps (setup : Setup base KemSK) (codec : Codec Reader Response)
    (work : OracleComp RegistrationRecordPrimitives.Spec Value) :
    Keeps (anchor := anchor) (simulateQ (RegistrationWorldRecords.handler (n := n) (Auxiliary := Auxiliary) setup codec) work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_keeps value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_keeps _ _ (records_query_keeps setup codec query) ih

private theorem capability_keeps (query : PqxdhRecordLiftInterface.Capability n) :
    Keeps (anchor := anchor) (RegistrationWorldServerCompletion.capability (Auxiliary := Auxiliary) query) := by
  intro before valid result supported
  simp only [RegistrationWorldServerCompletion.capability, StateT.run, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact valid.trans (RegistrationWorldCache.effects_cache (.inr query) before.world.1 inner possible)

private theorem signing_query_cache
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationSigningShared.Spec.Domain) (before : RegistrationWorldSigning.State n)
    (result : RegistrationSigningShared.Spec.Range query × RegistrationWorldSigning.State n)
    (supported : result ∈ support ((RegistrationWorldSigning.outgoing sign query).run before)) :
    before.1.primitive.2 ≤ result.2.1.primitive.2 := by
  cases query with
  | hash request =>
      simp only [RegistrationWorldSigning.outgoing, StateT.run, support_map] at supported
      obtain ⟨inner, reached, same⟩ := supported
      cases same
      exact RegistrationWorldCache.effects_cache _ before.1 inner reached
  | sign request payload digest =>
      simp only [RegistrationWorldSigning.outgoing, StateT.run, support_map] at supported
      obtain ⟨inner, reached, same⟩ := supported
      cases same
      exact (RegistrationWorldCache.sampled_cache (sign request) before.1 inner reached).ge

private theorem signing_program_cache {Output : Type}
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp RegistrationSigningShared.Spec Output) (before : RegistrationWorldSigning.State n)
    (result : Output × RegistrationWorldSigning.State n)
    (supported : result ∈ support ((simulateQ (RegistrationWorldSigning.outgoing sign) work).run before)) :
    before.1.primitive.2 ≤ result.2.1.primitive.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact le_refl _
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, queried, continued⟩ := supported
      exact (signing_query_cache sign query before middle queried).trans (ih middle.1 middle.2 result continued)

/-- Actual response hashing and every attempted signature extend the arbitrary earlier cache before any writer can fail. -/
private theorem signing (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseHash) :
    ∀ (before : State n Auxiliary), Valid (anchor := anchor) before → ∀ result,
      result ∈ support ((RegistrationWorldServerCompletion.signing sign encode pending).run before) → Valid (anchor := anchor) result.2 := by
  intro before valid result supported
  simp only [RegistrationWorldServerCompletion.signing, StateT.run, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact valid.trans (signing_program_cache sign (RegistrationWorldServerPublication.program encode pending) before.world inner possible)

private theorem install_keeps (control : pqxdh.ServerState) (published : registration.PublishedServerResponse Encoded) :
    Keeps (anchor := anchor) (RegistrationWorldServerCompletion.install (n := n) (Auxiliary := Auxiliary) control published) := by
  cases moved : peer.begin_peer_insert control published with
  | fail error | div =>
      unfold RegistrationWorldServerCompletion.install
      rw [moved]
      exact pure_keeps _
  | ok result => cases result with
    | Err previous =>
        unfold RegistrationWorldServerCompletion.install
        rw [moved]
        exact pure_keeps _
    | Ok pending =>
        rw [RegistrationWorldServerCompletion.install_native control published pending moved]
        exact bind_keeps _ _ (capability_keeps _) (fun _ => pure_keeps _)

/-- Native publication and peer insertion preserve the arbitrary earlier cache through success and failure. -/
private theorem publish (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (pending : registration.ServerResponseHash) :
    ∀ (before : State n Auxiliary), Valid (anchor := anchor) before → ∀ result,
      result ∈ support ((RegistrationWorldServerCompletion.publish sign encode control pending).run before) → Valid (anchor := anchor) result.2 := by
  have law : Keeps (anchor := anchor) (RegistrationWorldServerCompletion.publish sign encode control pending : StateT (State n Auxiliary) ProbComp _) := by
    unfold RegistrationWorldServerCompletion.publish
    apply bind_keeps _ _ (signing sign encode pending)
    intro result
    cases result with
    | fail error | div => exact pure_keeps _
    | ok outcome => cases outcome with
      | Err previous => exact pure_keeps _
      | Ok published => exact install_keeps control published
  exact law

/-- The actual complete record program extends its same source cache and changes no signing receipt. -/
theorem records (setup : Setup base KemSK) (codec : Codec Reader Response)
    (work : OracleComp RegistrationRecordPrimitives.Spec Value) (before : State n Auxiliary)
    (result : Value × State n Auxiliary)
    (supported : result ∈ support ((simulateQ (RegistrationWorldRecords.handler setup codec) work).run before)) :
    before.world.1.primitive.2 ≤ result.2.world.1.primitive.2 ∧ result.2.world.2 = before.world.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    cases supported
    exact ⟨le_refl _, rfl⟩
  | query_bind query next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, called, continued⟩ := supported
    simp only [RegistrationWorldRecords.handler, StateT.run, support_map] at called
    obtain ⟨inner, possible, same⟩ := called
    have first := shared_program_facts setup codec (RegistrationRecordPrimitives.callbacks setup.source query) before inner possible
    have next := ih middle.1 middle.2 result continued
    cases same
    exact ⟨first.1.trans next.1, next.2.trans first.2⟩

/-- Actual response signing, encoding and every peer-insertion outcome retain all cache entries at the preceding record cut. -/
theorem publication (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (pending : registration.ServerResponseHash) (before : State n Auxiliary)
    (result : RustM (RegistrationWorldServerCompletion.Result Encoded) × State n Auxiliary)
    (supported : result ∈ support ((RegistrationWorldServerCompletion.publish sign encode control pending).run before)) :
    before.world.1.primitive.2 ≤ result.2.world.1.primitive.2 :=
  publish sign encode control pending before (le_refl _) result supported

end BeaconcryptCore.Computational.RegistrationNativeWorldStageCache

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWorldStageCache.records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWorldStageCache.records

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWorldStageCache.publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWorldStageCache.publication
