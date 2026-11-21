-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedStartup
import BeaconcryptCore.Computational.RegistrationNativeSecretWordMessage

/-! Actual effectful native startup supplies the cold original frontend and an unused role map on the same reached World. Server ML generation and pure fixed pin construction retain the complete reached World cache. These facts are derived from the actual constructor/import AST and do not reset private World state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupFields
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (WorldSpec coinLift effectLift)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

/-- Literalizing existing references changes no native frontend field under any candidate evaluation. -/
def word {source : RegistrationNativeMldsa.Source} (before : RegistrationNativePublicFrontend.State source) :
    RegistrationNativeSecretWordMessage.State source :=
  ⟨⟨before.server.control, before.server.pin, before.server.consumed,
    before.server.sessions.map (Option.map (fun ready => ⟨ready.agreement, RegistrationNativeSecretWordMessage.literal ready.reference⟩))⟩,
    before.beacons, before.environment, before.parsedAccepts⟩

/-- The complete literal frontend evaluates to its exact original native state for every candidate. -/
theorem word_eval {source : RegistrationNativeMldsa.Source} (before : RegistrationNativePublicFrontend.State source)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) : (word before).eval candidate = before := by
  cases before with
  | mk server owners env parsed =>
    cases server with
    | mk control pin consumed sessions =>
      simp only [word, RegistrationNativeSecretWordMessage.State.eval, RegistrationNativeSecretWordMessage.ServerState.eval,
        List.map_map, Option.map_map, RegistrationNativeSecretWordMessage.ServerReady.eval,
        RegistrationNativeSecretWordMessage.eval_literal, Function.comp_def]
      congr 1
      congr 1
      have identity : (fun (value : Option RegistrationServerReferenceRoot.Ready) =>
          value.map (fun ready => (⟨ready.agreement, ready.reference⟩ : RegistrationServerReferenceRoot.Ready))) = id := by
        funext value
        cases value with
        | none => rfl
        | some ready => cases ready; rfl
      rw [identity, List.map_id]

/-- Every supported successful actual startup has the literal cold roster, session list and parsed-attempt counter. -/
theorem start_cold (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity) (started : RegistrationNativeHiddenStartup.Started source)
    (supported : some started ∈ support (RegistrationNativeHiddenStartup.start (n := n) setup source ensureInit identityIndex serverKeyId identity)) :
    started.native.frontend.server.sessions = [] ∧ started.native.frontend.beacons = [] ∧ started.native.frontend.parsedAccepts = 0 := by
  simp only [RegistrationNativeHiddenStartup.start, mem_support_bind_iff] at supported
  obtain ⟨constructed, _constructed, continued⟩ := supported
  cases built : constructed.1 with
  | none => simp only [built, mem_support_pure_iff] at continued; cases continued
  | some created =>
      simp only [built, mem_support_bind_iff] at continued
      obtain ⟨generated, _generated, continued⟩ := continued
      cases sampled : generated with
      | none => simp only [sampled, mem_support_pure_iff] at continued; cases continued
      | some credential =>
          simp only [sampled, mem_support_bind_iff] at continued
          obtain ⟨installed, _installed, returned⟩ := continued
          simp only [mem_support_pure_iff, Option.some.injEq] at returned
          cases returned
          exact ⟨rfl, rfl, rfl⟩

private def Allowed : (WorldSpec n).Domain → Prop
  | .inl _ => True
  | .inr (.inl (.inl _)) => True
  | .inr (.inl (.inr (.hash _))) => True
  | _ => False
instance : DecidablePred (Allowed (n := n)) := fun query => by
  rcases query with created | (coin | capability) | record
  · exact isTrue trivial
  · exact isTrue trivial
  · cases capability <;> simp only [Allowed] <;> infer_instance
  · exact isFalse id

private def fields (before : PqxdhRecordLiftWorld.State n) := (before.used, before.seeds)

private theorem sampled_used (work : ProbComp Value) (before : PqxdhRecordLiftWorld.State n)
    (result : Value × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.sampled work).run before)) : fields result.2 = fields before := by
  simp only [PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨actual, _possible, rfl⟩ := supported
  rfl

private theorem query_used (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain)
    (allowed : Allowed query) (before : PqxdhRecordLiftWorld.State n)
    (result : (WorldSpec n).Range query × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route query).run before)) :
    fields result.2 = fields before := by
  rcases query with created | (coin | capability) | record
  · simp only [CborRecordWorldSimulation.guarded, CborRecordWorldClient.refusal, PqxdhRecordLiftWorld.handler,
      PqxdhRecordLiftWorld.initializeServer, StateT.run] at supported
    split at supported <;> simp only [mem_support_pure_iff] at supported <;> cases supported <;> rfl
  · simp only [CborRecordWorldSimulation.guarded, CborRecordWorldClient.refusal, PqxdhRecordLiftWorld.handler,
      PqxdhRecordLiftWorld.effects, StateT.run] at supported
    exact sampled_used _ (PqxdhRecordLiftWorld.chargeEffect (.inl coin) before) result supported
  · cases capability <;> simp only [Allowed] at allowed
    rename_i bytes
    simp only [CborRecordWorldSimulation.guarded, CborRecordWorldClient.refusal, PqxdhRecordLiftWorld.handler,
        PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability, StateT.run, mem_support_bind_iff,
        mem_support_pure_iff] at supported
    obtain ⟨actual, called, rfl⟩ := supported
    exact sampled_used _ (PqxdhRecordLiftWorld.chargeEffect (.inr (.hash bytes)) before) actual called
  · cases allowed

private theorem program_used (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) Value)
    (bounded : work.IsQueryBoundP (fun query => ¬ Allowed query) 0)
    (before : PqxdhRecordLiftWorld.State n) (result : Value × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((simulateQ (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route) work).run before)) :
    fields result.2 = fields before := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      rfl
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      have allowed : Allowed query := by simpa only [not_not] using bounded.1.resolve_right (by omega)
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, called, continued⟩ := supported
      exact (ih middle.1 (by simpa using bounded.2 middle.1) middle.2 result continued).trans
        (query_used setup wire route query allowed before middle called)

private theorem coins_allowed (work : ProbComp Value) :
    (simulateQ (coinLift (n := n)) work).IsQueryBoundP (fun query => ¬ Allowed query) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ work 0 (isQueryBoundP_false work 0)
  intro coin
  simp [coinLift, Allowed, isQueryBoundP_query_iff]

private theorem start_allowed (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity) :
    (RegistrationNativeHiddenStartup.start (n := n) setup source ensureInit identityIndex serverKeyId identity).IsQueryBoundP (fun query => ¬ Allowed query) 0 := by
  unfold RegistrationNativeHiddenStartup.start
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0) (coins_allowed _) _
  intro constructed _possible
  cases constructed.1
  · trivial
  · apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0) (coins_allowed _) _
    intro generated _possible
    cases generated
    · trivial
    · apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0) _ _
      · simp [Allowed, isQueryBoundP_query_iff]
      · intro installed _possible
        trivial

/-- The same actual startup result has both cold frontend fields and an untouched role-use map; the reached shared cache is retained literally. -/
theorem initialized (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (seed : PqxdhJointIdentity.IdentitySeed) (started : RegistrationNativeHiddenStartup.Started source)
    (world : PqxdhRecordLiftWorld.State n)
    (supported : (some started, world) ∈ support (RegistrationNativeG3MaterializedStartup.startup setup wire route source ensureInit identityIndex serverKeyId seed)) :
    started.native.frontend.server.sessions = [] ∧ started.native.frontend.beacons = [] ∧ started.native.frontend.parsedAccepts = 0 ∧
      (∀ slot role, world.used slot role = false) ∧ world.seeds = PqxdhRecordLiftLazyTable.initial := by
  have openReached : some started ∈ support (RegistrationNativeHiddenStartup.start (n := n) setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed)) := by
    apply OracleComp.support_simulateQ_run'_subset
      (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route) _ PqxdhRecordLiftWorld.initial
    rw [StateT.run'_eq, support_map]
    exact ⟨(some started, world), supported, rfl⟩
  obtain ⟨sessions, owners, parsed⟩ := start_cold setup source ensureInit identityIndex serverKeyId _ started openReached
  have preserved := program_used setup wire route _
    (start_allowed setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed))
    PqxdhRecordLiftWorld.initial (some started, world) supported
  refine ⟨sessions, owners, parsed, ?_, ?_⟩
  · have used := congrArg Prod.fst preserved
    intro slot role
    exact congrFun (congrFun used slot) role
  · exact congrArg Prod.snd preserved

end BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupFields
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupFields.word_eval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupFields.word_eval
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupFields.start_cold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupFields.start_cold
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupFields.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupFields.initialized
