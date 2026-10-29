-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemServerPrimitive
import BeaconcryptCore.Computational.RegistrationNativeKemWorldAgreement

/-! The actual native Server agreement opens its literal KEM callback through the indexed service. Native request logs, complete private pool, local state, cache, populated bindings and capabilities remain. The only analysis projection is the proved private uniform ledger; its original resource bill is separate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemServerCompiler
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativeKemServerState (State mask)
open RegistrationNativeKemServerInterface (source get put modify withRole)
variable {ι KemSK Reader Response Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

def project (state : State n mlSource × PqxdhLiveKemBirth.Pool KemSK) := (mask state.1, state.2)

def logged (query : RegistrationAgreementExecutor.Request) (before : State n mlSource) : State n mlSource :=
  { before with server := { before.server with world := { before.server.world with
    requests := before.server.world.requests ++ RegistrationWorldAgreement.recorded query } } }

private theorem get_run (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (before : State n mlSource × PqxdhLiveKemBirth.Pool KemSK) :
    (simulateQ (source setup codec checks route verify representation created) get).run before =
      pure (mask before.1, project before) := by
  simp only [RegistrationNativeKemServerInterface.get, simulateQ_spec_query, source, RegistrationNativeKemInterface.source,
    RegistrationNativeKemServerInterface.other, StateT.run, map_pure, project]

private theorem put_run (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (before : State n mlSource × PqxdhLiveKemBirth.Pool KemSK)
    (next : State n mlSource) :
    (simulateQ (source setup codec checks route verify representation created) (put next)).run before =
      pure ((), (mask next, before.2)) := by
  simp only [put, simulateQ_spec_query, source, RegistrationNativeKemInterface.source,
    RegistrationNativeKemServerInterface.other, StateT.run, map_pure]

private theorem modify_run (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (before : State n mlSource × PqxdhLiveKemBirth.Pool KemSK)
    (change : State n mlSource → State n mlSource) :
    (simulateQ (source setup codec checks route verify representation created) (modify change)).run before =
      pure ((), (mask (change (mask before.1)), before.2)) := by
  simp only [RegistrationNativeKemServerInterface.modify, simulateQ_bind, StateT.run_bind]
  rw [get_run]
  simp only [pure_bind, put_run]
  rfl

noncomputable def nativeAgreement (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) :
    QueryImpl RegistrationAgreementExecutor.Spec (StateT (State n mlSource × PqxdhLiveKemBirth.Pool KemSK) ProbComp) :=
  fun query before => (fun result => (result.1,
    ({ before.1 with server := { before.1.server with world := result.2 } }, before.2))) <$>
      (RegistrationWorldAgreement.agreement setup.source
        (RegistrationServerRoleBackend.native setup checks representation created.seed) query).run before.1.server.world

private theorem native_canonical (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : RegistrationAgreementExecutor.Request)
    (before : State n mlSource × PqxdhLiveKemBirth.Pool KemSK) :
    Prod.map id project <$> (nativeAgreement setup checks representation created query).run before =
      (fun result => (result.1, (logged query (withRole (mask before.1) result.2), before.2))) <$>
        (RegistrationAgreementShared.auxiliary setup.source
          (RegistrationServerRoleBackend.native setup checks representation created.seed) query).run before.1.server.world.auxiliary := by
  have law := congrArg (fun work => (fun result => (result.1.1,
      ({ before.1 with server := { before.1.server with world :=
        ⟨result.1.2, before.1.server.world.requests ++ RegistrationWorldAgreement.recorded query,
          before.1.server.world.recordRequests, (result.2, before.1.server.world.world.2)⟩ } }, before.2))) <$> work)
    (RegistrationNativeKemWorldUniform.sampled_mask
      ((RegistrationAgreementShared.auxiliary setup.source
        (RegistrationServerRoleBackend.native setup checks representation created.seed) query).run
          before.1.server.world.auxiliary) before.1.server.world.world.1)
  simpa only [nativeAgreement, RegistrationWorldAgreement.agreement, StateT.run, Functor.map_map,
    Prod.map, id_eq, Function.comp_def, project, logged, withRole, mask,
    RegistrationNativeKemServerState.maskServer] using law

private theorem agreement_run (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : RegistrationAgreementExecutor.Request)
    (before : State n mlSource × PqxdhLiveKemBirth.Pool KemSK) :
    (simulateQ (source setup codec checks route verify representation created)
      (RegistrationNativeKemServerInterface.agreement setup checks query)).run before =
      (simulateQ (source setup codec checks route verify representation created)
        (RegistrationNativeKemServerInterface.agreementCore setup checks query)).run (logged query (mask before.1), before.2) := by
  simp only [RegistrationNativeKemServerInterface.agreement, simulateQ_bind, StateT.run_bind]
  rw [modify_run]
  simp only [pure_bind]
  rfl

private theorem primitive_call (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : RegistrationAgreementShared.PrimitiveRequest)
    (before : State n mlSource × PqxdhLiveKemBirth.Pool KemSK) :
    Prod.map id project <$>
        (nativeAgreement setup checks representation created query.toRequest).run before =
      (simulateQ (source setup codec checks route verify representation created)
        (RegistrationNativeKemServerInterface.agreement setup checks query.toRequest)).run (project before) := by
  have law := RegistrationNativeKemServerPrimitive.primitive_program setup codec checks route verify representation created
    (RegistrationAgreementShared.PrimitiveSpec.query query : OracleComp RegistrationAgreementShared.PrimitiveSpec _)
    (logged query.toRequest before.1) before.2
  rw [native_canonical, agreement_run]
  cases query <;>
    simp only [RegistrationAgreementShared.PrimitiveRequest.toRequest, RegistrationAgreementShared.auxiliary,
      RegistrationNativeKemServerInterface.agreementCore, simulateQ_spec_query, project, logged, withRole,
      mask, RegistrationNativeKemServerState.maskServer, RegistrationNativeKemWorldUniform.mask] at law ⊢ <;>
    convert law.symm using 1 <;> rfl

/-- Every actual native agreement callback has the same complete operational output through the exposed indexed KEM service. -/
theorem agreement_source (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : RegistrationAgreementExecutor.Request)
    (before : State n mlSource × PqxdhLiveKemBirth.Pool KemSK) :
    Prod.map id project <$> (nativeAgreement setup checks representation created query).run before =
      (simulateQ (source setup codec checks route verify representation created)
        (RegistrationNativeKemServerInterface.agreement setup checks query)).run (project before) := by
  cases query with
  | convertPublic key => exact primitive_call setup codec checks route verify representation created (.convertPublic key) before
  | convertSecret role => exact primitive_call setup codec checks route verify representation created (.convertSecret role) before
  | generate role => exact primitive_call setup codec checks route verify representation created (.generate role) before
  | encapsulate key => exact primitive_call setup codec checks route verify representation created (.encapsulate key) before
  | decapsulate ciphertext => exact primitive_call setup codec checks route verify representation created (.decapsulate ciphertext) before
  | dh request => exact primitive_call setup codec checks route verify representation created (.dh request) before
  | root request =>
      rw [native_canonical, agreement_run]
      simp only [RegistrationNativeKemServerInterface.agreementCore, RegistrationAgreementShared.auxiliary,
        StateT.run_pure, map_pure, simulateQ_pure, project, logged, RegistrationWorldAgreement.recorded, List.append_nil,
        withRole, mask, RegistrationNativeKemServerState.maskServer, RegistrationNativeKemWorldUniform.mask]

/-- The complete literal native controller, including every optional callback and actual Root32 request, factors through the selected-KEM source. -/
theorem agreement_program (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value)
    (before : State n mlSource × PqxdhLiveKemBirth.Pool KemSK) :
    Prod.map id project <$> (simulateQ (nativeAgreement setup checks representation created) work).run before =
      (simulateQ (source setup codec checks route verify representation created)
        (simulateQ (RegistrationNativeKemServerInterface.agreement setup checks) work)).run (project before) := by
  rw [← QueryImpl.simulateQ_compose]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project
    (agreement_source setup codec checks route verify representation created) work before

end BeaconcryptCore.Computational.RegistrationNativeKemServerCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemServerCompiler.agreement_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemServerCompiler.agreement_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemServerCompiler.agreement_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemServerCompiler.agreement_program
