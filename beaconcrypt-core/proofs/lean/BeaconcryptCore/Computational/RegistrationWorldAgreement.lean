-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationWorldSigning
import BeaconcryptCore.Computational.RegistrationRootStage
import BeaconcryptCore.Computational.RegistrationPostRootServices

/-!
Native agreement callbacks run alongside the actual World and signing receipts. Every underlying primitive coin is forwarded through the World's existing uniform counter. A separate chronological request list counts actual agreement calls, including optional failure; root HKDF calls are retained by the separate private family instrumentation, while the complete native auxiliary state is preserved. Agreement never creates a second CTX cache.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationWorldAgreement
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {Auxiliary ι KemSK Reader Response : Type} {base : OracleSpec ι}

/-- Chronological callback kinds retain actual attempts without copying private root or chain operands into optional instrumentation. -/
inductive RecordCall where
  | rootKdf | initialKdf | ratchetKdf | seal | hash | write | openAead
  deriving DecidableEq

def recordCall : RegistrationRecordPrimitives.Request → RecordCall
  | .rootKdf _ => .rootKdf
  | .initialKdf _ => .initialKdf
  | .ratchetKdf _ => .ratchetKdf
  | .seal _ => .seal
  | .hash _ => .hash
  | .write _ => .write
  | .openAead _ => .openAead

structure State (n : Nat) (Auxiliary : Type) where
  auxiliary : Auxiliary
  requests : List RegistrationAgreementExecutor.Request
  recordRequests : List RecordCall
  world : RegistrationWorldSigning.State n

def project (state : State n Auxiliary) : RawCtxSharedPrimitive.SharedState Auxiliary :=
  (state.auxiliary, state.world.1.primitive.2)

/-- Root calls are counted by the private related-family interpreter; their unavailable payload is not copied into this native primitive ledger. -/
def recorded : RegistrationAgreementExecutor.Request → List RegistrationAgreementExecutor.Request
  | .root _ => []
  | request => [request]

/-- Typed primitive calls retain their actual returned native state and charge every uniform query to the existing World. -/
noncomputable def agreement (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp)) :
    QueryImpl RegistrationAgreementExecutor.Spec (StateT (State n Auxiliary) ProbComp) :=
  fun query state =>
    (fun result => (result.1.1, State.mk result.1.2
      (state.requests ++ recorded query) state.recordRequests (result.2, state.world.2))) <$>
      (PqxdhRecordLiftWorld.sampled ((RegistrationAgreementShared.auxiliary source primitive query).run state.auxiliary)).run state.world.1

/-- Forgetting only instrumentation recovers the actual typed source primitive interpreter. -/
theorem agreement_project (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (query : RegistrationAgreementExecutor.Request) (state : State n Auxiliary) :
    Prod.map id project <$> (agreement source primitive query).run state =
      (RegistrationAgreementShared.implementation source primitive query).run (project state) := by
  have same := congrArg (fun work => (fun result => (result.1, (result.2, state.world.1.primitive.2))) <$> work)
    (PqxdhRecordLiftWorld.countCoin_forget
      ((RegistrationAgreementShared.auxiliary source primitive query).run state.auxiliary)
      state.world.1.primitive.1.uniform)
  simpa only [agreement, project, RegistrationAgreementShared.implementation,
    PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp, Functor.map_map, Prod.map, id_eq] using same

/-- Arbitrary source continuations retain all native auxiliary effects, rather than just a root output. -/
theorem agreement_program_project {Result : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (work : OracleComp RegistrationAgreementExecutor.Spec Result) (state : State n Auxiliary) :
    Prod.map id project <$> (simulateQ (agreement source primitive) work).run state =
      (simulateQ (RegistrationAgreementShared.implementation source primitive) work).run (project state) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project (agreement_project source primitive) work state

/-- Agreement callbacks retain the existing shared CTX table and every signing-attempt receipt. -/
theorem agreement_cache_receipts (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (query : RegistrationAgreementExecutor.Request) (state : State n Auxiliary)
    (result : RegistrationAgreementExecutor.Spec.Range query × State n Auxiliary)
    (supported : result ∈ support ((agreement source primitive query).run state)) :
    result.2.world.1.primitive.2 = state.world.1.primitive.2 ∧
      result.2.world.2 = state.world.2 ∧ result.2.requests = state.requests ++ recorded query := by
  simp only [agreement, PqxdhRecordLiftWorld.sampled, StateT.run,
    bind_pure_comp, Functor.map_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact ⟨rfl, rfl, rfl⟩

/-- The exact native source agreement program is executed in the instrumented World. -/
theorem server_project (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (control : pqxdh.ServerState) (authenticated : registration.AuthenticatedInit) (state : State n Auxiliary) :
    Prod.map id project <$>
      (simulateQ (agreement source primitive) (RegistrationAgreementExecutor.server control .Fresh authenticated)).run state =
      (simulateQ (RegistrationAgreementShared.implementation source primitive)
        (RegistrationAgreementExecutor.server control .Fresh authenticated)).run (project state) :=
  agreement_program_project source primitive _ state

abbrev Spec (n : Nat) (Encoded : Type) := RegistrationWorldSigning.Spec n Encoded + RegistrationAgreementExecutor.Spec

def worldLift {Encoded : Type} : QueryImpl (RegistrationWorldSigning.Spec n Encoded) (OracleComp (Spec n Encoded)) :=
  fun query => (Spec n Encoded).query (.inl query)

def agreementLift {Encoded : Type} : QueryImpl RegistrationAgreementExecutor.Spec (OracleComp (Spec n Encoded)) :=
  fun query => (Spec n Encoded).query (.inr query)

/-- The trusted native schedule retains the same World, signing history and actual primitive backend through interleaving. -/
noncomputable def handler {Encoded : Type} (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp)) :
    QueryImpl (Spec n Encoded) (StateT (State n Auxiliary) ProbComp)
  | .inl query => fun state => (fun result => (result.1, { state with world := result.2 })) <$>
      (RegistrationWorldSigning.handler setup codec route sign query).run state.world
  | .inr query => agreement setup.source primitive query

/-- Original World/authentication/signing continuations retain exactly their original instrumented execution. -/
theorem world_program_project {Encoded Result : Type} (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (work : OracleComp (RegistrationWorldSigning.Spec n Encoded) Result) (state : State n Auxiliary) :
    Prod.map id State.world <$>
      (simulateQ (handler setup codec route sign primitive) (simulateQ worldLift work)).run state =
      (simulateQ (RegistrationWorldSigning.handler setup codec route sign) work).run state.world := by
  have step : ∀ (query : (RegistrationWorldSigning.Spec n Encoded).Domain) (current : State n Auxiliary), Prod.map id State.world <$>
      (((handler setup codec route sign primitive) ∘ₛ worldLift) query).run current =
      (RegistrationWorldSigning.handler setup codec route sign query).run current.world := by
    intro query current
    simp only [QueryImpl.compose, worldLift, simulateQ_spec_query, handler, StateT.run,
      Functor.map_map, Prod.map, id_eq]
    exact id_map _
  simpa only [QueryImpl.simulateQ_compose] using
    OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ State.world step work state

end BeaconcryptCore.Computational.RegistrationWorldAgreement

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldAgreement.agreement_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldAgreement.agreement_project

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldAgreement.agreement_program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldAgreement.agreement_program_project

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldAgreement.agreement_cache_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldAgreement.agreement_cache_receipts

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldAgreement.server_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldAgreement.server_project

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldAgreement.world_program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldAgreement.world_program_project
