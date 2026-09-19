import BeaconcryptCore.Computational.PqxdhInitialLabelBuilder

/-!
The current authenticated-root continuation is a concrete ordinary initializer observer: the Server Ready root is erased, the actual post scheduler uses response-only root labels, and only the source interpretation reconstructs the selected root cache. The observer preserves full source order, optional replies and complete private state; its context is the actual preparation before the selected uniform-root draw.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialLegalObserver
open PqxdhJointKdfGame PqxdhKemIndCca PqxdhCorrelatedExpand PqxdhCorrelatedExpandHybrid
open PqxdhCorrelatedExtractFamily PqxdhInitializerSecrecy PqxdhChallengeSecretRouting
open PqxdhPhase2SourceAux PqxdhPhase1AcceptanceOracle PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPrivateKemSource
open PqxdhInitialRootLabelService PqxdhSecretInputKdf
variable {ι M P I D K X Response A KemSK Result : Type} {baseSpec : OracleSpec ι} {S B : Nat}

set_option backward.isDefEq.respectTransparency false in
/-- The actual Server builder's public coin embedding is exactly the original coin computation in the root interface. -/
theorem localCoins_source (fixed : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK) (challenge : MlKem768Ciphertext)
    (work : ProbComp Result) :
    simulateQ (rootPost fixed baseImpl kem secret challenge) (PqxdhPrivateAcceptedRoot.localCoins work) = rootCoins work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [PqxdhPrivateAcceptedRoot.localCoins, simulateQ_bind, simulateQ_spec_query]
      simp only [rootPost, publicImpl, kemAmbientImpl]
      change (rootCoins (unifSpec.query query : ProbComp _) >>= fun answer =>
        simulateQ (rootPost fixed baseImpl kem secret challenge) (PqxdhPrivateAcceptedRoot.localCoins (next answer))) = _
      rw [show rootCoins (unifSpec.query query >>= next) =
        (rootCoins (unifSpec.query query : ProbComp _) >>= fun answer => rootCoins (next answer)) from liftComp_bind _ _ _]
      simp only [ih]

/-- The full original post continuation is recovered by private cache reconstruction from the response-only observer, including every final role/private field and the complete original root cache. -/
theorem post_source
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (client : OracleComp (PqxdhPhase2SourceScheduler.Spec baseSpec S B) Result)
    (state : PqxdhPhase2PostScheduler.State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count)
    (selected : Message) (root : RootOutput) (cache : RootOracle.QueryCache) :
    Prod.map id (completeCache selected root) <$>
      (simulateQ (labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp) selected (realInitial fixed root))
        ((simulateQ (PqxdhInitialLabelPost.target attachedVerify primitives count fixed localImpl writer sender route decode baseImpl kem secret challenge) client).run state)).run cache =
      (simulateQ uniformImpl (simulateQ (rootPost fixed baseImpl kem secret challenge)
        ((simulateQ (PqxdhPhase2PostScheduler.target attachedVerify primitives count fixed localImpl writer sender route decode challenge) client).run state))).run
          (completeCache selected root cache) := by
  rw [complete_source, ← PqxdhInitialLabelCompiler.source_program, PqxdhInitialLabelPost.program_source]

section Current
open PqxdhAuthenticatedRootExperiment PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhSourceAuthenticatedRoot PqxdhPrivateAcceptedRoot

noncomputable def accepted {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (secret : KemSK) (selected : Message)
    (prepared : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State)
    (ready : Ready) : OracleComp PqxdhInitialLabelCompiler.Spec Bool := do
  let result ← PqxdhInitialLabelBuilder.build env.source env.recordWriter env.aux env.senderId env.index env.metadata selected ready prepared.1.context.selection.2
  Prod.fst <$> (simulateQ (PqxdhInitialLabelPost.target attachedVerify primitives 1 env.source env.localImpl
    env.recordWriter env.senderId env.route env.decode baseImpl kem secret ready.ciphertext)
    (post prepared.1.context.selection.1 result.1)).run (result.2, prepared.2)

/-- The entire current executable accepted-root observer, including its adaptive post scheduler, is independent of the erased Ready root field. -/
theorem accepted_root_unused {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (secret : KemSK) (selected : Message)
    (prepared : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State)
    (ready : Ready) (root : RootOutput) :
    accepted env baseImpl kem attachedVerify primitives program post secret selected prepared { ready with root := root } =
      accepted env baseImpl kem attachedVerify primitives program post secret selected prepared ready := rfl

/-- The actual current accepted-root continuation, including its real Server build and every adaptive post callback, is recovered from the root-erased response-only observer by private root-cache reconstruction. -/
theorem accepted_source {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (secret : KemSK) (selected : Message)
    (prepared : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State)
    (ready : Ready) (cache : RootOracle.QueryCache) :
    Prod.map id (completeCache selected ready.root) <$>
      (simulateQ (labelledFull env.source (QueryImpl.ofLift unifSpec ProbComp) selected (realInitial env.source ready.root))
        (accepted env baseImpl kem attachedVerify primitives program post secret selected prepared ready)).run cache =
      (simulateQ uniformImpl (simulateQ (rootPost env.source baseImpl kem secret ready.ciphertext)
        (targetAccepted env attachedVerify primitives program post prepared ready))).run
          (completeCache selected ready.root cache) := by
  simp only [accepted, targetAccepted, simulateQ_bind, StateT.run_bind, map_bind,
    PqxdhInitialLabelBuilder.build_source, localCoins_source, PqxdhInitialRootContext.coins_complete, bind_map_left]
  apply bind_congr
  intro result
  have complete := post_source attachedVerify primitives 1 env.source env.localImpl
    env.recordWriter env.senderId env.route env.decode baseImpl kem secret ready.ciphertext
    (post prepared.1.context.selection.1 result.1) (result.2, prepared.2) selected ready.root cache
  have projected := congrArg (Functor.map (fun pair => (pair.1.1, pair.2))) complete
  simpa only [simulateQ_map, StateT.run_map, Functor.map_map, Prod.map, id_eq] using projected

noncomputable def acceptedDecision {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (secret : KemSK) (selected : Message)
    (prepared : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State)
    (ready : Ready) (response : PqxdhInitialRootLabelService.Response) : ProbComp Bool :=
  (simulateQ (labelledFull env.source (QueryImpl.ofLift unifSpec ProbComp) selected response)
    (accepted env baseImpl kem attachedVerify primitives program post secret selected prepared ready)).run' ∅

/-- The source decision at the actual first-miss cache is exactly the selected-response observer decision; only the source interpreter receives the selected raw root cache entry. -/
theorem accepted_decision_source {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (secret : KemSK) (selected : Message)
    (prepared : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State)
    (ready : Ready) :
    acceptedDecision env baseImpl kem attachedVerify primitives program post secret selected prepared
      (PqxdhInitialBuilderCut.eraseRoot ready) (realInitial env.source ready.root) =
      (simulateQ uniformImpl (simulateQ (rootPost env.source baseImpl kem secret ready.ciphertext)
        (targetAccepted env attachedVerify primitives program post prepared ready))).run'
          ((∅ : RootOracle.QueryCache).cacheQuery selected ready.root) := by
  have complete := congrArg (Functor.map Prod.fst)
    (accepted_source env baseImpl kem attachedVerify primitives program post secret selected prepared ready ∅)
  simpa only [acceptedDecision, StateT.run'_eq, Functor.map_map, Prod.map_fst, id_eq,
    completeCache, PqxdhInitialBuilderCut.eraseRoot, accepted_root_unused] using complete

/-- Concrete pre-expansion context: the entire current root preparation, including the private KEM interpreter data, precedes the independent root draw. -/
abbrev Context {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1)) :=
  PqxdhCorrelatedExtractFamily.Prepared (protocol env kem attachedVerify primitives program post) KemSK

noncomputable def observe {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (context : Context env kem attachedVerify primitives program post)
    (response : PqxdhInitialRootLabelService.Response) : ProbComp Bool :=
  match context.state with
  | .completed decision => pure decision
  | .pending prepared ephemeral =>
      let selected := coordinates (serverCoordinates env.source.crypto env.server.ikSk ephemeral.toList
        prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.before.publicKey prepared.1.context.generated.after.publicKey)
      acceptedDecision env baseImpl kem attachedVerify primitives program post context.secretKey selected prepared
        (ready env.server env.application prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.after.publicKey
          ephemeral context.ciphertext (List.Vector.replicate 32 0)) response

/-- The actual first-miss root continuation equals this ordinary response observer fed a fresh independent32-byte root; completed branches ignore that sample in the evaluated distribution. -/
theorem first_miss_observer {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (context : Context env kem attachedVerify primitives program post) :
    𝒟[($ᵗ RootOutput) >>= fun root => observe env baseImpl kem attachedVerify primitives program post context (realInitial env.source root)] =
      𝒟[Prod.fst <$> PqxdhInitialRootContext.firstMiss env.source baseImpl kem (protocol env kem attachedVerify primitives program post) context] := by
  cases mode : context.state with
  | completed decision =>
      simp only [observe, mode, PqxdhInitialRootContext.firstMiss, protocol,
        PqxdhInitialRootContext.afterRoot, simulateQ_pure, StateT.run_pure, map_pure]
      exact OracleComp.ProgramLogic.Relational.evalDist_bind_const_of_no_failure _ _
  | pending prepared ephemeral =>
      simp only [observe, mode, PqxdhInitialRootContext.firstMiss, protocol,
        PqxdhInitialRootContext.afterRoot, map_bind]
      apply congrArg evalDist
      apply bind_congr
      intro root
      have same := accepted_decision_source env baseImpl kem attachedVerify primitives program post context.secretKey
        (coordinates (serverCoordinates env.source.crypto env.server.ikSk ephemeral.toList
          prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.before.publicKey prepared.1.context.generated.after.publicKey))
        prepared (ready env.server env.application prepared.1.context.publicIdentity.ed25519
          prepared.1.context.generated.after.publicKey ephemeral context.ciphertext root)
      simpa only [StateT.run'_eq, PqxdhInitialBuilderCut.eraseRoot, ready] using same

noncomputable def sample {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1)) :
    ProbComp (Context env kem attachedVerify primitives program post × RootOutput) := do
  let context ← PqxdhCorrelatedExtractFamily.prepare baseImpl kem (protocol env kem attachedVerify primitives program post)
  let root ← $ᵗ RootOutput
  pure (context, root)

/-- The complete current uniform-root endpoint supplies this exact independent-root sampler and root-free initializer observer. The extra ignored root sample in completed branches is an evaluated-distribution comparison and is billed separately. -/
theorem current_game {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1)) :
    𝒟[sample env baseImpl kem attachedVerify primitives program post >>= fun pair =>
      observe env baseImpl kem attachedVerify primitives program post pair.1 (realInitial env.source pair.2)] =
      𝒟[uniformGame (PqxdhCorrelatedExpand.rootReduction env.source baseImpl kem
        (protocol env kem attachedVerify primitives program post))] := by
  simp only [sample, bind_assoc, pure_bind, PqxdhInitialRootContext.current_game, map_bind]
  exact evalDist_bind_congr' (m := ProbComp) _ (first_miss_observer env baseImpl kem attachedVerify primitives program post)

end Current
end BeaconcryptCore.Computational.PqxdhInitialLegalObserver

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialLegalObserver.localCoins_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialLegalObserver.localCoins_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialLegalObserver.post_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialLegalObserver.post_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialLegalObserver.accepted_root_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialLegalObserver.accepted_root_unused

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialLegalObserver.accepted_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialLegalObserver.accepted_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialLegalObserver.accepted_decision_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialLegalObserver.accepted_decision_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialLegalObserver.first_miss_observer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialLegalObserver.first_miss_observer

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialLegalObserver.current_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialLegalObserver.current_game
