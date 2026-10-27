import BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler

/-! Actual three-message target signing history and its preservation by the native continuation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityLog
open PqxdhJointIdentity PqxdhEd25519EufCma PqxdhServerAuthExperiment
open PqxdhServerAuthJointIdentityCompiler
open PqxdhJointGapDh (ScalarBytes PublicChallenge)
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The three actual signature requests and their real returned signatures, in source order. -/
def signingEvents (primitives : Primitives) (seed : IdentitySeed) (keys : Phase1KeyTuple) : History :=
  [.signed (prekeyMessage keys.prekey) (primitives.sign seed (prekeyMessage keys.prekey)),
   .signed (oneTimeMessage keys.oneTime) (primitives.sign seed (oneTimeMessage keys.oneTime)),
   .signed (pqMessage keys.pqKey) (primitives.sign seed (pqMessage keys.pqKey))]

/-- One real signing call appends its exact request and returned signature to the challenger history. -/
theorem sign_run (primitives : Primitives) (seed : IdentitySeed) (message : Pqxdh.Bytes) (history : History) :
    (jointImpl primitives seed (.inr (.sign message))).run history =
      pure (primitives.sign seed message, history ++ [.signed message (primitives.sign seed message)]) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The literal Phase1 compiler retains the complete source output and appends exactly three real signing events, including on writer refusal. -/
theorem phase1_history (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (seed : IdentitySeed) (publicValue : PublicChallenge) (oneTime : ScalarBytes)
    (kemPk : PqxdhKemIndCca.MlKem768PublicKey) (kemSk : KemSK) (history : History) :
    (simulateQ (jointImpl setup.joint seed)
      (phase1 setup codec (setup.joint.publicKeys seed) publicValue oneTime kemPk kemSk)).run history =
    (fun result => (result, history ++ signingEvents setup.joint seed
      ⟨publicValue.prekey, setup.dh.publicKey oneTime, kemPk⟩)) <$>
        phase1Run setup codec seed publicValue oneTime kemPk kemSk := by
  simp only [phase1, phase1Run, PqxdhLivePhase1Bundle.bundle, freshBeacon,
    simulateQ_bind, simulateQ_spec_query, signingImpl, phase1Impl,
    pure_bind]
  simp only [PqxdhLivePhase1Bundle.afterGenerated, PqxdhBeaconPhase1Publication.prepare,
    Option.map_some, publicProjection, projection, PqxdhLivePhase1Bundle.signing,
    PqxdhJointPhase1SourceWriter.signingProgram, simulateQ_bind, simulateQ_spec_query,
    signingImpl, phase1Impl, simulateQ_map, StateT.run_bind, StateT.run_map, pure_bind]
  rw [sign_run]
  simp only [map_pure, pure_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    signingImpl, simulateQ_map, StateT.run_bind, StateT.run_map]
  rw [sign_run]
  simp only [map_pure, pure_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    signingImpl, simulateQ_map, StateT.run_bind, StateT.run_map, StateT.run_pure]
  rw [sign_run, map_pure, pure_bind]
  simp only [pure_bind, Option.map_some, PqxdhLivePhase1Bundle.writing,
    PqxdhBeaconPhase1Publication.afterSigning, PqxdhBeaconPhase1Publication.prepare,
    simulateQ_bind, simulateQ_spec_query, signingImpl, phase1Impl, signingEvents, List.append_assoc, List.cons_append, List.nil_append]
  split <;> simp only [simulateQ_pure, StateT.run_pure, map_pure]


/-- The exact subset of joint requests that issue a signature. -/
def IsSign : AdversarySpec.Domain → Prop
  | .inr (.sign _) => True
  | _ => False

instance : DecidablePred IsSign := fun query => by
  rcases query with coin | (message | peer) <;> simp only [IsSign] <;> infer_instance

/-- A complete interpreted program issues no signatures when every actual callback issues none. -/
theorem simulate_quiet {κ Result : Type} {spec : OracleSpec κ}
    (implementation : QueryImpl spec (OracleComp AdversarySpec))
    (quiet : ∀ query, (implementation query).IsQueryBoundP IsSign 0) (work : OracleComp spec Result) :
    (simulateQ implementation work).IsQueryBoundP IsSign 0 := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact isQueryBoundP_bind (n := 0) (m := 0) (quiet query) (fun reply _ => ih reply)

/-- Every local native sampler retains all of its uniform work and issues no signature. -/
theorem coins_quiet {Result : Type} (work : ProbComp Result) :
    (coins work).IsQueryBoundP IsSign 0 := by
  apply simulate_quiet
  intro query
  simp only [isQueryBoundP_query_iff, IsSign, false_implies]

set_option backward.isDefEq.respectTransparency false in
/-- Native preparation can perform local KEM work and target static DH, but cannot issue a new target signature. -/
theorem auxiliary_quiet (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : (PqxdhBeaconPhase2Preparation.Spec Unit (Unit ⊕ ScalarBytes) KemSK Unit Response).Domain) :
    (auxiliary setup codec query).IsQueryBoundP IsSign 0 := by
  cases query <;> simp only [auxiliary, isQueryBoundP_pure, coins_quiet,
    isQueryBoundP_map_iff, isQueryBoundP_query_iff, IsSign, false_implies]
  rename_i pair point
  cases pair <;> trivial

set_option backward.isDefEq.respectTransparency false in
/-- The selected-prekey wrapper retains the signature-free property of every actual preparation callback. -/
theorem prefix_quiet (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (scalar : ScalarBytes)
    (query : (PqxdhBeaconPhase2Preparation.Spec Unit (Unit ⊕ (Unit ⊕ ScalarBytes)) KemSK Unit Response).Domain)
    (state : Unit) : ((prefixImpl setup codec scalar query).run state).IsQueryBoundP IsSign 0 := by
  cases query <;> simp only [prefixImpl, PqxdhPhase2GapDhSource.nativeImpl, StateT.run_lift, bind_pure_comp,
    isQueryBoundP_map_iff]
  all_goals try exact auxiliary_quiet setup codec _
  rename_i pair point
  cases pair <;> simp only [StateT.run, StateT.lift, bind_pure_comp, isQueryBoundP_map_iff]
  all_goals first | exact auxiliary_quiet setup codec _ | trivial

/-- The entire original preparation, including every rejection and locally interpreted KEM query, makes no signing request. -/
theorem prepare_quiet (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (scalar : ScalarBytes) (control : pqxdh.BeaconInitSent) (identity : Unit)
    (oneTime : Unit ⊕ ScalarBytes) (kem : KemSK) (raw : Pqxdh.Bytes) :
    (prepare setup codec scalar control identity oneTime kem raw).IsQueryBoundP IsSign 0 := by
  simp only [prepare, StateT.run'_eq, isQueryBoundP_map_iff]
  exact (isQueryBoundP_false _ 0).simulateQ_run_StateT_of_step
    (fun query state => by simpa only [ite_false] using prefix_quiet setup codec scalar query state) ()

/-- The full native stage continues locally after preparation and adds no signing capability. -/
theorem stage_quiet (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (serverSeed : IdentitySeed) (scalar : ScalarBytes) (control : pqxdh.BeaconInitSent)
    (identity : Unit) (oneTime : Unit ⊕ ScalarBytes) (kem : KemSK) (raw : Pqxdh.Bytes)
    (state : PqxdhServerAuthNative.NativeState KemSK) :
    ((stage setup codec serverSeed scalar control identity oneTime kem raw).run state).IsQueryBoundP IsSign 0 := by
  simp only [stage, StateT.run]
  apply isQueryBoundP_bind (n := 0) (m := 0) (prepare_quiet setup codec scalar control identity oneTime kem raw)
  rintro (_ | original) _
  · trivial
  · exact coins_quiet _

/-- Every active or inactive finish branch preserves the absence of new signing requests, including rejected preparation and final abort. -/
theorem finish_quiet (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (serverSeed : IdentitySeed) (scalar : ScalarBytes) (raw : Pqxdh.Bytes)
    (state : PqxdhServerAuthNative.NativeState KemSK) :
    ((finish setup codec serverSeed scalar raw).run state).IsQueryBoundP IsSign 0 := by
  simp only [finish, StateT.run]
  cases state.2.beacon.beacon.phase <;> simp only [isQueryBoundP_pure]
  rename_i control prekey oneTime kem
  apply isQueryBoundP_bind (n := 0) (m := 0)
    (stage_quiet setup codec serverSeed scalar control state.2.beacon.beacon.identity oneTime kem raw state)
  intro result _
  trivial

set_option backward.isDefEq.respectTransparency false in
/-- No exposed native API callback can issue a target signature after Phase1. -/
theorem handler_quiet (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (scalar : ScalarBytes) (query : ServerAuthSpec.Domain)
    (state : PqxdhServerAuthNative.NativeState KemSK) :
    ((handler setup codec checks serverSeed scalar query).run state).IsQueryBoundP IsSign 0 := by
  rcases query with coin | (raw | build | raw | hmac | bytes | key)
  all_goals simp only [handler, StateT.run]
  all_goals first | exact coins_quiet _ | exact finish_quiet setup codec serverSeed scalar _ state

/-- The entire adaptive public continuation is signature-free, irrespective of its schedule or private native state. -/
theorem program_quiet {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (scalar : ScalarBytes) (work : OracleComp ServerAuthSpec Result)
    (state : PqxdhServerAuthNative.NativeState KemSK) :
    ((simulateQ (handler setup codec checks serverSeed scalar) work).run state).IsQueryBoundP IsSign 0 := by
  exact (isQueryBoundP_false work 0).simulateQ_run_StateT_of_step
    (fun query state => by simpa only [ite_false] using handler_quiet setup codec checks serverSeed scalar query state) state

set_option backward.isDefEq.respectTransparency false in
/-- A signature-free continuation preserves the exact signed-message log while retaining every uniform computation and optional DH event in the same run. -/
theorem quiet_history {Result : Type} (primitives : Primitives) (seed : IdentitySeed)
    (work : OracleComp AdversarySpec Result) (quiet : work.IsQueryBoundP IsSign 0)
    (history : History) (result : Result × History)
    (supported : result ∈ support ((simulateQ (jointImpl primitives seed) work).run history)) :
    signedMessages result.2 = signedMessages history := by
  induction work using OracleComp.inductionOn generalizing history result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    rfl
  | query_bind query next ih =>
    simp only [isQueryBoundP_query_bind_iff, Nat.zero_sub, ite_self] at quiet
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
    obtain ⟨reply, reached, supported⟩ := (mem_support_bind_iff _ _ _).mp supported
    have suffix := ih reply.1 (quiet.2 reply.1) reply.2 result supported
    rw [suffix]
    rcases query with coin | (message | point)
    · simp only [jointImpl, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at reached
      obtain ⟨answer, _, rfl⟩ := reached
      rfl
    · exact ((quiet.1.resolve_right (Nat.lt_irrefl 0)) trivial).elim
    · simp only [jointImpl, StateT.run, primitiveReply, requestEvent, mem_support_pure_iff] at reached
      subst reply
      simp [signedMessages, List.filterMap_append]

set_option backward.isDefEq.respectTransparency false in
/-- One actual full Phase1/API execution has exactly the original three signed messages; arbitrary prior joint history and all later DH events remain in the same run. -/
theorem execution_history {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed beaconSeed : IdentitySeed) (scalar oneTime : ScalarBytes)
    (keys : PqxdhKemIndCca.MlKem768PublicKey × KemSK)
    (work : AuthInput → OracleComp ServerAuthSpec Result) (history : History)
    (result : ((Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK) ×
      (Result × PqxdhServerAuthNative.NativeState KemSK)) × History)
    (supported : result ∈ support ((simulateQ (jointImpl setup.joint beaconSeed)
      (execution setup codec checks serverSeed scalar oneTime keys work (setup.joint.publicKeys beaconSeed))).run history)) :
    signedMessages result.2 = signedMessages history ++
      [prekeyMessage (setup.dh.publicKey scalar), oneTimeMessage (setup.dh.publicKey oneTime), pqMessage keys.1] := by
  simp only [execution, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    phase1_history, bind_map_left, mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨published, _, middle, reached, rfl⟩ := supported
  simpa [signedMessages, signingEvents, List.filterMap_append, PqxdhJointGapDh.challenge] using
    quiet_history setup.joint beaconSeed _ (program_quiet setup codec checks serverSeed scalar _ _) _ middle reached

set_option backward.isDefEq.respectTransparency false in
/-- Local sampling preserves every joint event, including the original signatures and DH replies. -/
theorem coins_history {Result : Type} (primitives : Primitives) (seed : IdentitySeed)
    (work : ProbComp Result) (history : History) :
    (simulateQ (jointImpl primitives seed) (coins work)).run history =
      (fun result => (result, history)) <$> work := by
  induction work using OracleComp.inductionOn generalizing history with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [coins, simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at *
    simp only [jointImpl, StateT.run, bind_assoc, pure_bind, map_bind]
    exact bind_congr (fun answer => ih answer history)

end BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityLog

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityLog.sign_run' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityLog.sign_run
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityLog.phase1_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityLog.phase1_history
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityLog.simulate_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityLog.simulate_quiet
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityLog.coins_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityLog.coins_quiet
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityLog.auxiliary_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityLog.auxiliary_quiet
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityLog.prefix_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityLog.prefix_quiet
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityLog.prepare_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityLog.prepare_quiet
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityLog.stage_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityLog.stage_quiet
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityLog.finish_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityLog.finish_quiet
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityLog.handler_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityLog.handler_quiet
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityLog.program_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityLog.program_quiet
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityLog.quiet_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityLog.quiet_history
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityLog.execution_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityLog.execution_history
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityLog.coins_history' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityLog.coins_history
