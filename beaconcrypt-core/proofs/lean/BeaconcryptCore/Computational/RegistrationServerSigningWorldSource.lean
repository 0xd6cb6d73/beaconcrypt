-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerRecordWorldSource

/-! Actual outgoing native ML hash/sign callbacks and their open Env compiler share the same complete source-view World and chronological signing attempts. Every source signing draw is retained; only the explicit native/coin instrumentation and record-kind log are omitted by the view. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerSigningWorldSource
open RegistrationServerRecordWorldSource (project)
variable {n : Nat} {Auxiliary Value : Type}

noncomputable def source
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl RegistrationSigningShared.Spec (StateT (RegistrationWorldAgreement.State n Auxiliary) ProbComp) :=
  fun query before => (fun result => (result.1, { before with world := result.2 })) <$>
    (RegistrationWorldSigning.outgoing sign query).run before.world

noncomputable def compiler (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl RegistrationSigningShared.Spec (StateT (RegistrationWorldAgreement.State n Auxiliary) ProbComp) :=
  fun query before => (fun result => (result.1.1, { before with world := (result.2, result.1.2) })) <$>
    (simulateQ PqxdhRecordLiftWorld.effects
      ((RegistrationBoundSourceCompiler.compiler hkdf writer sign (.inr query)).run before.world.2)).run before.world.1

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := by
  change (work before >>= fun result => pure (observe result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

/-- Actual source hash/sign attempts ignore the omitted analysis coordinates and preserve every other local field. -/
theorem source_query
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationSigningShared.Request) (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id project <$> (source sign query).run before = (source sign query).run (project before) := by
  cases query with
  | hash request =>
      have native := congrArg (fun distribution => (fun result => (result.1,
        { project before with world := (result.2, before.world.2) })) <$> distribution)
        (RegistrationNativeWorldView.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request) before.world.1)
      simpa only [source, RegistrationWorldSigning.outgoing, StateT.run, Functor.map_map, Prod.map_def, id_eq,
        project] using native
  | sign request payload digest =>
      have native := congrArg (fun distribution => (fun result => (result.1,
        { project before with world := (result.2, before.world.2 ++
          [(⟨⟨request.public_key, payload, BeaconcryptCore.Refinement.RegistrationSigningTrace.replyBytes result.1⟩, digest⟩ : RegistrationSigningShared.Receipt)]) })) <$> distribution)
        (RegistrationNativeWorldView.sampled (sign request) before.world.1)
      simpa only [source, RegistrationWorldSigning.outgoing, StateT.run, Functor.map_map, Prod.map_def, id_eq,
        project] using native

/-- The compiled actual signing callback has the same native source reply, cache, draw bill and attempt receipt; compiled Env coin charges are explicitly projected. -/
theorem compiler_query (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationSigningShared.Request) (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id project <$> (compiler hkdf writer sign query).run before = (source sign query).run (project before) := by
  cases query with
  | hash request =>
      have native := congrArg (fun distribution => (fun result => (result.1,
        { project before with world := (result.2, before.world.2) })) <$> distribution)
        (RegistrationNativeWorldView.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request) before.world.1)
      simp only [compiler, RegistrationBoundSourceCompiler.compiler, source,
        RegistrationWorldSigning.outgoing, PqxdhDeploymentEnvironment.request, simulateQ_map,
        simulateQ_spec_query, StateT.run, Functor.map_map, Prod.map_def, id_eq, project, state_map_apply] at native ⊢
      exact native
  | sign request payload digest =>
      have native := congrArg (fun distribution => (fun result => (result.1,
        { project before with world := (result.2, before.world.2 ++
          [(⟨⟨request.public_key, payload, BeaconcryptCore.Refinement.RegistrationSigningTrace.replyBytes result.1⟩, digest⟩ : RegistrationSigningShared.Receipt)]) })) <$> distribution)
        (RegistrationNativeWorldView.coins (sign request) before.world.1)
      simp only [compiler, RegistrationBoundSourceCompiler.compiler, source,
        RegistrationWorldSigning.outgoing, PqxdhDeploymentEnvironment.coins, simulateQ_map, StateT.run,
        Functor.map_map, Prod.map_def, id_eq, project, state_map_apply] at native ⊢
      exact native

/-- Arbitrary actual source publication/signing programs retain the complete semantic native state. -/
theorem source_program
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp RegistrationSigningShared.Spec Value) (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id project <$> (simulateQ (source sign) work).run before =
      (simulateQ (source sign) work).run (project before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project (source_query sign) work before

/-- The entire open signing compiler has that same source program, including failed signatures and late publication rejection. -/
theorem compiler_program (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp RegistrationSigningShared.Spec Value) (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id project <$> (simulateQ (compiler hkdf writer sign) work).run before =
      (simulateQ (source sign) work).run (project before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project (compiler_query hkdf writer sign) work before

end BeaconcryptCore.Computational.RegistrationServerSigningWorldSource

/-- info: 'BeaconcryptCore.Computational.RegistrationServerSigningWorldSource.source_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerSigningWorldSource.source_query
/-- info: 'BeaconcryptCore.Computational.RegistrationServerSigningWorldSource.compiler_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerSigningWorldSource.compiler_query
/-- info: 'BeaconcryptCore.Computational.RegistrationServerSigningWorldSource.source_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerSigningWorldSource.source_program
/-- info: 'BeaconcryptCore.Computational.RegistrationServerSigningWorldSource.compiler_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerSigningWorldSource.compiler_program
