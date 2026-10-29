-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationWorldCache
import BeaconcryptCore.Computational.RegistrationWorldAuthentication
import BeaconcryptCore.Computational.RegistrationSigningShared

/-!
The native signing schedule runs alongside the actual instrumented record World. Its separate private receipt list records actual signing attempts, while every outgoing hash uses the World's existing CTX cache and every signing coin uses its actual uniform counter. The projection to the shared signing interpreter is proved from these operations. Public-key protection remains a separate key-family condition.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false

namespace BeaconcryptCore.Computational.RegistrationWorldSigning

open PqxdhRecordLiftInterface
open PqxdhServerAuthExperiment (Setup Codec)
open BeaconcryptCore.Refinement.RegistrationSigningTrace (replyBytes)
open BeaconcryptCore.Refinement.RegistrationInputs (hashBytes)
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

abbrev State (n : Nat) := PqxdhRecordLiftWorld.State n × List RegistrationSigningShared.Receipt

def project (state : State n) : RegistrationSigningShared.State :=
  (state.2, state.1.primitive.2)

/-- Outgoing hash and signing callbacks retain complete World state and chronological attempt receipts. -/
noncomputable def outgoing (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl RegistrationSigningShared.Spec (StateT (State n) ProbComp)
  | .hash request => fun state =>
      (fun result => (result.1, (result.2, state.2))) <$>
        (PqxdhRecordLiftWorld.effects (.inr (.hash (hashBytes request)))).run state.1
  | .sign request payload digest => fun state =>
      (fun result => (result.1, (result.2,
        state.2 ++ [⟨⟨request.public_key, payload, replyBytes result.1⟩, digest⟩]))) <$>
        (PqxdhRecordLiftWorld.sampled (sign request)).run state.1

/-- The actual instrumented callbacks project to the existing shared-cache signing interpreter, without a simulation premise. -/
theorem outgoing_project
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationSigningShared.Spec.Domain) (state : State n) :
    Prod.map id project <$> (outgoing sign query).run state =
      (RegistrationSigningShared.implementation sign query).run (project state) := by
  cases query with
  | hash request =>
    have same := congrArg (fun work => (fun result : CtxRomAuth.CtxDigest × RawCtxSharedPrimitive.SharedState Unit =>
      (result.1, (state.2, result.2.2))) <$> work)
      (RegistrationWorldAuthentication.hash_project (hashBytes request) state.1)
    simpa only [outgoing, RegistrationSigningShared.implementation, MldsaSharedNative.authentication,
      project, RegistrationWorldAuthentication.project, StateT.run, bind_pure_comp,
      Functor.map_map, Prod.map, id_eq] using same
  | sign request payload digest =>
    have same := congrArg (fun work => (fun reply =>
      (reply, (state.2 ++ [RegistrationSigningShared.Receipt.mk
        ⟨request.public_key, payload, replyBytes reply⟩ digest], state.1.primitive.2))) <$> work)
      (PqxdhRecordLiftWorld.countCoin_forget (sign request) state.1.primitive.1.uniform)
    simpa only [outgoing, RegistrationSigningShared.implementation, PqxdhRecordLiftWorld.sampled,
      project, StateT.run, bind_pure_comp, Functor.map_map, Prod.map, id_eq] using same

/-- Every complete outgoing source continuation has the same reply, receipt log and cache after forgetting only World instrumentation. -/
theorem outgoing_program_project {Result : Type}
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp RegistrationSigningShared.Spec Result) (state : State n) :
    Prod.map id project <$> (simulateQ (outgoing sign) work).run state =
      (simulateQ (RegistrationSigningShared.implementation sign) work).run (project state) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project (outgoing_project sign) work state

/-- Actual outgoing dispatch derives receipt validity in the instrumented World, including failed signing or publication. -/
theorem dispatch_cached {Encoded : Type}
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (command : BeaconcryptCore.Refinement.RegistrationSigningTrace.Command) (encoded : core.option.Option Encoded)
    (state : State n) (cached : RegistrationSigningShared.Cached (project state))
    (result : RustM (BeaconcryptCore.Refinement.RegistrationSigningTrace.DispatchResult Encoded) × State n)
    (supported : result ∈ support ((simulateQ (outgoing sign)
      (RegistrationSigningShared.dispatch command encoded)).run state)) :
    RegistrationSigningShared.Cached (project result.2) := by
  have projected : (result.1, project result.2) ∈ support
      ((simulateQ (RegistrationSigningShared.implementation sign)
        (RegistrationSigningShared.dispatch command encoded)).run (project state)) := by
    rw [← outgoing_program_project sign (RegistrationSigningShared.dispatch command encoded) state, support_map]
    exact ⟨result, supported, rfl⟩
  exact RegistrationSigningShared.dispatch_cached sign command encoded (project state) cached _ projected

/-- This is a private native scheduling interface; the public adversary reaches it through its source compiler. -/
abbrev Spec (n : Nat) (Encoded : Type) := WorldSpec n + RegistrationSigningShared.SigningSpec Encoded

def worldLift {Encoded : Type} : QueryImpl (WorldSpec n) (OracleComp (Spec n Encoded)) :=
  fun query => (Spec n Encoded).query (.inl query)

noncomputable def handler {Encoded : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl (Spec n Encoded) (StateT (State n) ProbComp)
  | .inl query => fun state =>
      (fun result => (result.1, (result.2, state.2))) <$>
        (PqxdhRecordLiftWorld.handler setup codec route query).run state.1
  | .inr (command, encoded) => simulateQ (outgoing sign) (RegistrationSigningShared.dispatch command encoded)

/-- Native authentication/record programs forwarded through this schedule retain exactly their original World execution. -/
theorem world_program_project {Encoded Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (WorldSpec n) Result) (state : State n) :
    Prod.map id Prod.fst <$>
        (simulateQ (handler setup codec route sign) (simulateQ (worldLift (Encoded := Encoded)) work)).run state =
      (simulateQ (PqxdhRecordLiftWorld.handler setup codec route) work).run state.1 := by
  have step : ∀ query (current : State n), Prod.map id Prod.fst <$>
        (((handler (Encoded := Encoded) setup codec route sign) ∘ₛ worldLift) query).run current =
      (PqxdhRecordLiftWorld.handler setup codec route query).run current.1 := by
    intro query current
    simp only [QueryImpl.compose, worldLift, simulateQ_spec_query, handler, StateT.run,
      Functor.map_map, Prod.map, id_eq, Prod.mk.eta]
    exact id_map _
  simpa only [QueryImpl.simulateQ_compose] using
    OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst step work state

/-- Actual World operations preserve earlier signing receipts, and actual outgoing dispatch derives each new receipt. -/
theorem query_cached {Encoded : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (Spec n Encoded).Domain) (state : State n)
    (cached : RegistrationSigningShared.Cached (project state))
    (result : (Spec n Encoded).Range query × State n)
    (supported : result ∈ support ((handler setup codec route sign query).run state)) :
    RegistrationSigningShared.Cached (project result.2) :=
  match query with
  | .inl native =>
    match OracleComp.mem_support_map_peel _
      ((PqxdhRecordLiftWorld.handler setup codec route native).run state.1) supported with
    | ⟨inner, reached, same⟩ => same.symm ▸
        RegistrationSigningShared.cached_extend state.2 state.1.primitive.2 inner.2.primitive.2
          (RegistrationWorldCache.handler_cache setup codec route native state.1 inner reached) cached
  | .inr (command, encoded) => dispatch_cached sign command encoded state cached result supported

/-- Arbitrary adaptive native schedules retain the hash receipts of every actual signing attempt. -/
theorem program_cached {Encoded Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (Spec n Encoded) Result) (state : State n)
    (cached : RegistrationSigningShared.Cached (project state))
    (result : Result × State n)
    (supported : result ∈ support ((simulateQ (handler setup codec route sign) work).run state)) :
    RegistrationSigningShared.Cached (project result.2) :=
  simulateQ_run_preservesInv (handler setup codec route sign)
    (fun current => RegistrationSigningShared.Cached (project current))
    (fun query current valid after reached => query_cached setup codec route sign query current valid after reached)
    work state cached result supported

/-- The complete native schedule starts with the original empty World and an empty private attempt log. -/
noncomputable def run {Encoded Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (Spec n Encoded) Result) : ProbComp (Result × State n) :=
  (simulateQ (handler setup codec route sign) work).run (PqxdhRecordLiftWorld.initial, [])

/-- Receipt validity follows from actual execution, without an input history invariant. -/
theorem run_cached {Encoded Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (Spec n Encoded) Result) (result : Result × State n)
    (supported : result ∈ support (run setup codec route sign work)) :
    RegistrationSigningShared.Cached (project result.2) :=
  program_cached setup codec route sign work (PqxdhRecordLiftWorld.initial, [])
    (by simp only [project, RegistrationSigningShared.Cached, List.not_mem_nil, IsEmpty.forall_iff, implies_true])
    result supported

/-- Every reached per-key history is cached in the actual global World, with all failed attempts retained. -/
theorem run_history_cached {Encoded Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (Spec n Encoded) Result) (publicKey : Pqxdh.Bytes) (result : Result × State n)
    (supported : result ∈ support (run setup codec route sign work)) :
    MldsaSharedAuthentication.HistoryCached result.2.1.primitive.2
      (RegistrationSigningShared.historyFor publicKey (project result.2)) :=
  RegistrationSigningShared.history_cached publicKey (project result.2)
    (run_cached setup codec route sign work result supported)

/-- Outgoing callbacks preserve every earlier shared-cache entry, including a failed signature reply. -/
theorem outgoing_cache
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationSigningShared.Spec.Domain) (state : State n)
    (result : RegistrationSigningShared.Spec.Range query × State n)
    (supported : result ∈ support ((outgoing sign query).run state)) :
    state.1.primitive.2 ≤ result.2.1.primitive.2 := by
  cases query with
  | hash request =>
    simp only [outgoing, StateT.run, support_map] at supported
    obtain ⟨inner, member, rfl⟩ := supported
    exact RegistrationWorldCache.effects_cache (.inr (.hash (hashBytes request))) state.1 inner member
  | sign request payload digest =>
    simp only [outgoing, StateT.run, support_map] at supported
    obtain ⟨inner, member, rfl⟩ := supported
    exact (RegistrationWorldCache.sampled_cache (sign request) state.1 inner member).ge

/-- A complete actual signing continuation preserves a frozen earlier cache. -/
theorem outgoing_program_cache {Result : Type}
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp RegistrationSigningShared.Spec Result) (state : State n) (result : Result × State n)
    (supported : result ∈ support ((simulateQ (outgoing sign) work).run state)) :
    state.1.primitive.2 ≤ result.2.1.primitive.2 :=
  simulateQ_run_preservesInv (outgoing sign) (fun current => state.1.primitive.2 ≤ current.1.primitive.2)
    (fun query current earlier after reached => earlier.trans (outgoing_cache sign query current after reached))
    work state (le_refl _) result supported

/-- World and signing requests extend the same actual cache. -/
theorem query_cache {Encoded : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (Spec n Encoded).Domain) (state : State n) (result : (Spec n Encoded).Range query × State n)
    (supported : result ∈ support ((handler setup codec route sign query).run state)) :
    state.1.primitive.2 ≤ result.2.1.primitive.2 := by
  cases query with
  | inl native =>
    simp only [handler, StateT.run, support_map] at supported
    obtain ⟨inner, member, rfl⟩ := supported
    exact RegistrationWorldCache.handler_cache setup codec route native state.1 inner member
  | inr signing => exact outgoing_program_cache sign (RegistrationSigningShared.dispatch signing.1 signing.2) state result supported

/-- Every adaptive continuation retains the cache entries of the actual reached prefix. -/
theorem program_cache {Encoded Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (Spec n Encoded) Result) (state : State n) (result : Result × State n)
    (supported : result ∈ support ((simulateQ (handler setup codec route sign) work).run state)) :
    state.1.primitive.2 ≤ result.2.1.primitive.2 :=
  simulateQ_run_preservesInv (handler setup codec route sign)
    (fun current => state.1.primitive.2 ≤ current.1.primitive.2)
    (fun query current earlier after reached => earlier.trans (query_cache setup codec route sign query current after reached))
    work state (le_refl _) result supported

/-- Freeze the history at verification's prefix: later signing calls cannot change the list used for that origin trial. -/
theorem frozen_history_cached {Encoded Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (Spec n Encoded) Result) (state : State n)
    (cached : RegistrationSigningShared.Cached (project state)) (publicKey : Pqxdh.Bytes)
    (result : Result × State n)
    (supported : result ∈ support ((simulateQ (handler setup codec route sign) work).run state)) :
    MldsaSharedAuthentication.HistoryCached result.2.1.primitive.2
      (RegistrationSigningShared.historyFor publicKey (project state)) :=
  RegistrationSigningShared.history_cached publicKey (state.2, result.2.1.primitive.2)
    (RegistrationSigningShared.cached_extend state.2 state.1.primitive.2 result.2.1.primitive.2
      (program_cache setup codec route sign work state result supported) cached)

/-- The frozen prefix premise of a native origin trial is derived from the actual whole execution's two supported pieces. -/
theorem run_prefix_history_cached {Encoded First Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (first : OracleComp (Spec n Encoded) First) (next : First → OracleComp (Spec n Encoded) Result)
    (publicKey : Pqxdh.Bytes) (cut : First × State n) (cutReached : cut ∈ support (run setup codec route sign first))
    (result : Result × State n)
    (supported : result ∈ support ((simulateQ (handler setup codec route sign) (next cut.1)).run cut.2)) :
    MldsaSharedAuthentication.HistoryCached result.2.1.primitive.2
      (RegistrationSigningShared.historyFor publicKey (project cut.2)) :=
  frozen_history_cached setup codec route sign (next cut.1) cut.2
    (run_cached setup codec route sign first cut cutReached) publicKey result supported

end BeaconcryptCore.Computational.RegistrationWorldSigning

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldSigning.outgoing_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldSigning.outgoing_project

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldSigning.outgoing_program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldSigning.outgoing_program_project

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldSigning.dispatch_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldSigning.dispatch_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldSigning.world_program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldSigning.world_program_project

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldSigning.query_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldSigning.query_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldSigning.program_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldSigning.program_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldSigning.run_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldSigning.run_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldSigning.run_history_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldSigning.run_history_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldSigning.outgoing_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldSigning.outgoing_cache

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldSigning.outgoing_program_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldSigning.outgoing_program_cache

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldSigning.query_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldSigning.query_cache

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldSigning.program_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldSigning.program_cache

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldSigning.frozen_history_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldSigning.frozen_history_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldSigning.run_prefix_history_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldSigning.run_prefix_history_cached
