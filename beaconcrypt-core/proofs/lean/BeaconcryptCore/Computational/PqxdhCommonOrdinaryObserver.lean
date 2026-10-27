import BeaconcryptCore.Computational.PqxdhAuthenticatedRootExperiment

/-!
The original common observer is interpreted through the unblocked ordinary prechallenge interface. These equalities keep arbitrary common decisions and the actual registration builder; they introduce no target honesty or final-event premise.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhCommonOrdinaryObserver
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhPhase2GeneratedDriver PqxdhGeneratedBeaconState PqxdhAuthenticatedRootExperiment
open PqxdhPrivateAcceptedRoot PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhPhase1AcceptanceOracle
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhCorrelatedExpand
variable {ι : Type} {baseSpec : OracleSpec ι} {M P I D K X Response A Result : Type} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives) (count : Nat)

set_option backward.isDefEq.respectTransparency false in
/-- Unblocked common local coins retain their original ordinary CCA uniform interface. -/
theorem coins (work : ProbComp Result) :
    simulateQ (sourcePost (baseSpec := baseSpec) source none) (localCoins work) = ccaCoins work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [localCoins, ccaCoins, simulateQ_bind, simulateQ_spec_query]
    change (((MlKemCCAOracleSpec baseSpec).query (.inl (.inl query)) : OracleComp (MlKemCCAOracleSpec baseSpec) _) >>= fun answer =>
      simulateQ (sourcePost source none) (localCoins (next answer))) = _
    simp only [ih]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The exact source selector lift has the ordinary unblocked request interpretation. -/
theorem selector_step (query : (SelectorSpec baseSpec).Domain) (state : BareState count) :
    simulateQ (sourcePost source none)
      ((simulateQ (localSourceImpl source attachedVerify primitives count) (selectorLift query)).run state) =
    (borrowedSelector attachedVerify primitives count query).run state := by
  cases query with
  | inl request =>
    simp only [selectorLift, simulateQ_spec_query]
    change simulateQ (sourcePost source none) (localCoins ((bareImpl attachedVerify primitives count request).run state)) =
      ccaCoins ((bareImpl attachedVerify primitives count request).run state)
    exact coins source _
  | inr request =>
    simp only [selectorLift, simulateQ_spec_query]
    change simulateQ (sourcePost (baseSpec := baseSpec) source none)
      (do let answer ← ((PqxdhChallengeSecretRouting.LocalPostSpec baseSpec).query (.inl request) : OracleComp (PqxdhChallengeSecretRouting.LocalPostSpec baseSpec) _); pure (answer, state)) =
      (do let answer ← ((MlKemCCAOracleSpec baseSpec).query request : OracleComp (MlKemCCAOracleSpec baseSpec) _); pure (answer, state))
    simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, sourcePost]
    rfl

/-- Every public selector operation retains the actual joint identity state, original base requests and unblocked decapsulation results. -/
theorem selector_program (client : OracleComp (SelectorSpec baseSpec) Result) (state : BareState count) :
    simulateQ (sourcePost source none)
      ((simulateQ (localSourceImpl source attachedVerify primitives count) (simulateQ selectorLift client)).run state) =
    (simulateQ (borrowedSelector attachedVerify primitives count) client).run state := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [selector_step]
    apply bind_congr
    intro result
    exact ih result.1 result.2


set_option backward.isDefEq.respectTransparency false in
/-- The complete source common schedule becomes the literal ordinary scheduler, retaining arbitrary final decisions and all private state until the original projection. -/
theorem schedule (writer : RawCtxMixedShared.Writer) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (localImpl : QueryImpl (PqxdhPhase2SourceAux.LocalSpec I D K X Response) (StateT A ProbComp))
    (client : OracleComp (PqxdhPhase2SourceScheduler.Spec baseSpec S B) Result)
    (state : PqxdhPhase2SourceScheduler.State M P I D K A S B) (identities : BareState count) :
    simulateQ (sourcePost source none) (Prod.fst <$>
      (simulateQ (localSourceImpl source attachedVerify primitives count)
        (simulateQ selectorLift (Prod.fst <$>
          (simulateQ (PqxdhPhase2SourceScheduler.compiler source writer sender route decode localImpl) client).run state))).run identities) =
      Prod.fst <$> (simulateQ (PqxdhPhase2SourceScheduler.ordinary attachedVerify primitives count source writer sender route decode localImpl) client).run
        (PqxdhPhase2OldSource.packState state identities) := by
  simp only [simulateQ_map, StateT.run_map]
  rw [selector_program]
  simp only [Functor.map_map]
  have full := congrArg (Functor.map Prod.fst)
    (PqxdhPhase2SourceScheduler.compiler_complete attachedVerify primitives count source writer sender route decode localImpl client state identities)
  simpa only [Functor.map_map] using full

variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))

/-- Every completed common branch runs the original unblocked source schedule and preserves its actual decision. -/
theorem completed (output : PqxdhPrivateCandidateAcceptance.Outcome
      (PqxdhPrivatePhase1Prefix.Retained setup Unit (driver env.toDriverEnvironment program).State))
    (execution : PqxdhSourceAuthenticatedRoot.ServerExecution) (identities : BareState count) :
    observe env.source none attachedVerify primitives count setup (commonObserver env program post) (some output) execution identities =
      Prod.fst <$> (simulateQ (PqxdhPhase2SourceScheduler.ordinary attachedVerify primitives count env.source env.recordWriter env.senderId env.route env.decode env.localImpl)
        (post output.context.selection.1 (RustM.ok none))).run (PqxdhPhase2OldSource.packState output.context.selection.2 identities) := by
  exact schedule env.source attachedVerify primitives count env.recordWriter env.senderId env.route env.decode env.localImpl
    (post output.context.selection.1 (RustM.ok none)) output.context.selection.2 identities

/-- The concrete builder's private coin channel is exactly the original selector lift. -/
theorem lifted_coins (work : ProbComp Result) :
    PqxdhProtocolRegistration.coins (baseSpec := baseSpec) work =
      simulateQ selectorLift (PqxdhProtocolSelector.coins work) := by
  unfold PqxdhProtocolRegistration.coins PqxdhProtocolSelector.coins
  rw [← QueryImpl.simulateQ_compose]
  congr 1

/-- The full builder computation retains the actual identity state and every original uniform call under the unblocked interpreter. -/
theorem builder_coins (work : ProbComp Result) (state : BareState count) :
    simulateQ (sourcePost (baseSpec := baseSpec) source none)
      ((simulateQ (localSourceImpl source attachedVerify primitives count) (PqxdhProtocolRegistration.coins work)).run state) =
      ccaCoins ((fun result => (result, state)) <$> work) := by
  rw [lifted_coins, selector_program, PqxdhPhase2SourceAux.borrowed_coins]

set_option backward.isDefEq.respectTransparency false in
/-- Accepted common candidates run the actual native registration builder and then their full original unblocked source schedule. -/
theorem accepted (output : PqxdhPrivateCandidateAcceptance.Outcome
      (PqxdhPrivatePhase1Prefix.Retained setup Unit (driver env.toDriverEnvironment program).State))
    (ready : Ready) (identities : BareState count) :
    acceptedObserve env.source none attachedVerify primitives count setup (commonObserver env program post) (some output) ready identities = (do
      let result ← ccaCoins ((PqxdhRegistrationProtocolState.build env.source env.recordWriter env.aux env.senderId
        env.index env.metadata ready).run output.context.selection.2)
      Prod.fst <$> (simulateQ (PqxdhPhase2SourceScheduler.ordinary attachedVerify primitives count env.source env.recordWriter env.senderId env.route env.decode env.localImpl)
        (post output.context.selection.1 result.1)).run (PqxdhPhase2OldSource.packState result.2 identities)) := by
  simp only [acceptedObserve, localAccepted, commonObserver, simulateQ_bind, StateT.run_bind, simulateQ_map, map_bind]
  rw [builder_coins]
  simp only [ccaCoins, simulateQ_map, bind_map_left]
  apply bind_congr
  intro result
  simpa only [simulateQ_map, StateT.run_map, Functor.map_map] using
    schedule env.source attachedVerify primitives count env.recordWriter env.senderId env.route env.decode env.localImpl
      (post output.context.selection.1 result.1) result.2 identities

end BeaconcryptCore.Computational.PqxdhCommonOrdinaryObserver


/-- info: 'BeaconcryptCore.Computational.PqxdhCommonOrdinaryObserver.coins' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCommonOrdinaryObserver.coins

/-- info: 'BeaconcryptCore.Computational.PqxdhCommonOrdinaryObserver.selector_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCommonOrdinaryObserver.selector_step

/-- info: 'BeaconcryptCore.Computational.PqxdhCommonOrdinaryObserver.selector_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCommonOrdinaryObserver.selector_program

/-- info: 'BeaconcryptCore.Computational.PqxdhCommonOrdinaryObserver.schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCommonOrdinaryObserver.schedule

/-- info: 'BeaconcryptCore.Computational.PqxdhCommonOrdinaryObserver.completed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCommonOrdinaryObserver.completed

/-- info: 'BeaconcryptCore.Computational.PqxdhCommonOrdinaryObserver.lifted_coins' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCommonOrdinaryObserver.lifted_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhCommonOrdinaryObserver.builder_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCommonOrdinaryObserver.builder_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhCommonOrdinaryObserver.accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCommonOrdinaryObserver.accepted
